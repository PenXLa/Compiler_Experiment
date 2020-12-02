#include <set>
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
#include <iterator>
#include <cstring>
#include <stack>
#include <fstream>
#include <sstream>
#include <functional>
using namespace std;
typedef long long LL;


//�﷨����㣬���ڴ����﷨�������ڲ鿴�Ƶ�����
struct grammar_tree_node {
    int word;
    vector<grammar_tree_node*> ch;
    ~grammar_tree_node() {
        for (grammar_tree_node* nd : ch) delete nd;
    }
};

enum pre_def_words {EPSLION = 0, ENDSYM = 1}; //�������Ϳ��֡��������е��ķ�����Ҫ�������ַ������Զ��嵽�����
//����ʽ���ս���ͷ��ս������int��ʾ��
//�����Ƿ��ս�����Ǹ������ս����Ҳ���Ǵʷ������׶εõ���sym
//����ʽ��A->��1|��2...
struct formular {
    int A;
    vector<vector<int>> alphas; //һ��vector<int>��ʾ��һ����ѡʽ������һ��vector���Ǻ�ѡʽ����

    bool operator < (const formular& f2) const {
        return A != f2.A ? alphas < f2.alphas : A < f2.A;
    }

    formular(int a, initializer_list<initializer_list<int>> alps) {
        A = a;
        for (const auto& alpha : alps) {
            alphas.push_back(vector<int>());
            for (int word : alpha) {
                alphas.back().push_back(word);
            }
        }
    }
};



class grammar {
public:
    set<formular> g;
    set<int> nter, ter; //���ս�����ս��
    int s; //��ʼ����
    char tbl[200][200]; //���ȹ�ϵ��,'<'��ʾ<��'='��ʾ=��'>'��ʾ>��0��ʾδ����


    grammar(int s, initializer_list<formular> formulars): s(s) {
        for (const formular& fml : formulars) { 
            g.insert(fml);
            nter.insert(fml.A); //����ʽ�󲿼�����ս����
            for (const auto& alpha : fml.alphas) 
                for (int word : alpha)
                    if (word < 0) nter.insert(word); //С��0���Ƿ��ս����������ս����
                    else ter.insert(word); //>=0�����ս���������ս����
        }
        calc_firstvt(); //Ԥ������ս����first��
        calc_lastvt();//Ԥ������ս����follow��
        memset(tbl, 0, sizeof tbl);
        build_table(); //����Ԥ�������
        build_reduceVN();
    }
//private:
    //��set1�в���x�����ز����set1�Ƿ�ı�
    bool set_ins(set<int>& set1, int x) {
        if (set1.count(x)) return false;
        set1.insert(x);
        return true;
    }
    //��set1�в���set2�����ز����set1�Ƿ�ı�
    bool set_ins(set<int>& set1, const set<int>& set2) {
        if (includes(set1.cbegin(), set1.cend(), set2.cbegin(), set2.cend())) return false;
        set1.insert(set2.begin(), set2.end());
        return true;
    }

    map<int, set<int>> fst, lst; //���ս����firstvt��lastvt

    //������ս����firstvt
    void calc_firstvt() {
        bool changed = false;
        do {
            changed = false;
            for (const formular& fml : g) { //��������ʽ
                for (const auto& alpha : fml.alphas) { //������ѡʽ
                    if (alpha[0]>=0) changed |= set_ins(fst[fml.A], alpha[0]); //P->a�����
                    else {
                        changed |= set_ins(fst[fml.A], fst[alpha[0]]); //P->Q�����
                        if (alpha.size() > 1) changed |= set_ins(fst[fml.A], alpha[1]);//������ڵڶ����ַ���������������ķ����壬�ض��Ƿ��ս��
                    }
                }
            }
        } while (changed);
    }
    //Ԥ������ս����lastvt
    void calc_lastvt() {
        bool changed = false;
        do {
            changed = false;
            for (const formular& fml : g) { //��������ʽ
                for (const auto& alpha : fml.alphas) { //������ѡʽ
                    if (alpha.back()>0) changed |= set_ins(lst[fml.A], alpha.back()); //P->...a�����
                    else {
                        changed |= set_ins(lst[fml.A], lst[alpha.back()]); //P->...Q�����
                        if (alpha.size() > 1) changed |= set_ins(lst[fml.A], alpha[alpha.size()-2]);//������ڵڶ����ַ���������������ķ����壬�ض��Ƿ��ս��
                    }
                }
            }
        } while (changed);
    }
    

    void build_table() {
        for (const formular& fml : g) { //��������ʽ
            for (const auto& alpha : fml.alphas) { //������ѡʽ
                for (int i=1; i<alpha.size()-1; ++i) //����aQb�����
                    if (alpha[i]<0 && alpha[i-1]>=0 && alpha[i+1]>=0) 
                        tbl[alpha[i-1]][alpha[i+1]] = '=';
                for (int i=1; i<alpha.size(); ++i) { //����ab��aQ��Qb
                    if (alpha[i]<0 && alpha[i-1]<0) 
                        tbl[alpha[i-1]][alpha[i]] = '='; //ab
                    else if (alpha[i-1]>=0 && alpha[i]<0)  //aQ
                        for (int vt : fst[alpha[i]]) 
                            tbl[alpha[i-1]][vt] = '<';
                    else if (alpha[i-1]<0 && alpha[i]>=0)  //Qb
                        for (int vt : lst[alpha[i-1]]) 
                            tbl[vt][alpha[i]]= '>';
                    else throw "Error";//�����������ķ��ս��
                }
            }
        }
    }

    map<vector<int>, int> reduceVN; //��������ķ��Ĺ�Լ��Ϊ�˷���parse����ʹ�ã�key��stack�������
    void build_reduceVN() { 
        for (const formular& fml : g) { //��������ʽ
            for (const auto& alpha : fml.alphas) { //������ѡʽ
                vector<int> alphavt;
                for (int i=alpha.size(); i>=0; --i) if (alpha[i]>=0) 
                    alphavt.push_back(alpha[i]);
                reduceVN[alphavt] = fml.A;
            }
        }
    }
};

//��ȡ�ʷ������Ľ��
//����ȡtoken��id������ȡʵ������
vector<int> read_tokens(string file) {
    vector<int> tokens;
    int id; string word;
    ifstream fin("tokens.txt");
    while(fin >> id >> word) {
        tokens.push_back(id);
    }
    fin.close();
    tokens.push_back(ENDSYM); //׷��һ��������
    return tokens;
}


//************���ķ�����*******************
//Ϊ�˱��뷽�㣬������symŪ��enum����Ҫ��0��1����ֹ��EPSLION��ENDSYM��ֵ��ͬ��
enum words {
//�ս��
ADD = 2,    MUL = 3,    LB = 4,
RB  = 5,    I   = 6,
//���ս��
E   = -1,   E1  = -2,   T = -3,     F   = -5,
};
//����ʽ
grammar g(E1, {
    formular(E1,     {{ENDSYM, E, ENDSYM}}),
    formular(E,     {{E, ADD, T}, {T}}),
    formular(T,     {{T, MUL, F}, {F}}),
    formular(F,     {{LB, E, RB}, {I}})
});
map<int, string> id2name = {
    {E, "E"}, {T, "T"}, {F, "F"}, 
    {I, "i"}, {ADD, "+"}, {MUL, "*"}, {LB, "("}, {RB, ")"}, {EPSLION, "��"}, {ENDSYM, "#"}
}; //���ڰ��ķ��ַ���IDת���ɱ��ڹ۲�ķ��ţ����ý����Ǳ��ڹ۲�����������㷨����û��Ӱ�졣
//************���ķ�����*******************



int getTopVT(const vector<int>& stk) {
    if (stk.back() >= 0) return stk.back();
    return stk[stk.size()-2];
}
void outputStack(const vector<int>& stk, const vector<int>& syms, int i) {
    for (int j=0; j<stk.size(); ++j) cout << id2name[stk[j]];
    for (int j=0; j<16-stk.size(); ++j) cout << ' ';

    for (int j=i+1; j<syms.size(); ++j) cout << id2name[syms[j]];
    for (int j=0; j<16-(syms.size()-i-1); ++j) cout << ' ';
}
//symջ���﷨��ջ���Ժϲ�Ϊ1��������Ϊ�˽����﷨�����Ϳ��ӻ�֮�����ϣ��ֳ���2��ջ
void parse(grammar& g, const vector<int>& syms) {
    printf("%-16s%-16s%-10s\n%-16s%", "Stack", "input", "Action", "#");
    for (int word : syms) cout << id2name[word]; 
    for (int j=0; j<16-syms.size(); ++j) cout << ' '; cout << "Prepare\n";


    vector<int> stk, prime; //����ջ���ض�����ʱջ.������������ķ����Է��ս�������ã����Է���ջ���Բ��ټ�����ս����
    stk.push_back(ENDSYM);
    for (int i=0; i<syms.size(); ++i) {
        while (g.tbl[getTopVT(stk)][syms[i]] == '>') {
            vector<int> poplist; //��ջ�ķ��ţ������������
            do {
                if (stk.back() < 0) poplist.push_back(stk.back()), stk.pop_back(); 
                poplist.push_back(stk.back());
                prime.push_back(stk.back()); 
                stk.pop_back();
            } while(g.tbl[getTopVT(stk)][prime.back()] == '=');
            if (stk.back() < 0) poplist.push_back(stk.back()), stk.pop_back(); //�������һ�����ս��

            int reduce = g.reduceVN[prime];
            stk.push_back(reduce);
            while(!prime.empty()) prime.pop_back();

            outputStack(stk, syms, i);
            cout << "Reduce " << id2name[reduce] << "->";
            for (int j=poplist.size()-1; j>=0; --j) cout << id2name[poplist[j]];
            cout << '\n'; 
            
        }
        stk.push_back(syms[i]);

        outputStack(stk, syms, i);
        cout << "Shift\n";
    }
}

void prtOPTable(grammar& g) {
    cout << "  ";
    for (const auto& r : id2name) if (r.first>0) cout << r.second << ' '; 
    cout << '\n';
    for (const auto& r : id2name) if (r.first>0) {
        cout << r.second << ' ';
        for (const auto& c : id2name) if (c.first>0)
            cout << (g.tbl[r.first][c.first]?g.tbl[r.first][c.first]:'.') << ' ';
        cout << '\n';
    }
}


int main(){
    vector<int> tokens = read_tokens("tokens.txt"); //���ļ�����ʷ������Ľ��
    prtOPTable(g);

    parse(g, tokens); //�﷨����

    system("pause");
    return 0;
}
