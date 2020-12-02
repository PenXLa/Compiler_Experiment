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
    
};


struct parse_exception : public exception {
    int row;
    string msg;
    parse_exception(int row, const string& msg): row(row), msg(msg) { }
    const char* what() const throw() { return ""; }
};
//symջ���﷨��ջ���Ժϲ�Ϊ1��������Ϊ�˽����﷨�����Ϳ��ӻ�֮�����ϣ��ֳ���2��ջ
grammar_tree_node* parse(const grammar& g, const vector<int>& syms) {
    stack<int> stk, prime; //����ջ���ض�����ʱջ.������������ķ����Է��ս�������ã����Է���ջ���ټ�����ս��
    stk.push(ENDSYM);
    for (int i=0; syms[i]!=ENDSYM; ++i) {
        if (g.tbl[stk.top()][syms[i]] == '') {

        }
    }
}

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
    {I, "i"}, {ADD, "+"}, {MUL, "*"}, {LB, "("}, {RB, ")"}, {EPSLION, "��"}
}; //���ڰ��ķ��ַ���IDת���ɱ��ڹ۲�ķ��ţ����ý����Ǳ��ڹ۲�����������㷨����û��Ӱ�졣
//************���ķ�����*******************

string getTreeJson(grammar_tree_node* root) {
    vector<grammar_tree_node*> nodes;
    vector<pair<grammar_tree_node*, grammar_tree_node*>> edges;
    function<void(grammar_tree_node*)> dfs;
    dfs = [&nodes, &edges, &dfs](grammar_tree_node* u){
        if (u != nullptr) {
            nodes.push_back(u);
            for (grammar_tree_node* v : u->ch) {
                edges.push_back(make_pair(u, v));
                dfs(v);
            }
        }
    };
    dfs(root);
    stringstream ss;
    ss << "{\"kind\": { \"graph\": true },\"nodes\": [";
    for (int i=0; i<nodes.size(); ++i) 
        ss << "{ \"id\": \"" << nodes[i] << "\",\"label\": \"" << id2name[nodes[i]->word] << "\" }" << ",\n"[i==nodes.size()-1];
    ss << "],\"edges\": [";
    for (int i=0; i<edges.size(); ++i) 
        ss << "{ \"from\": \"" << edges[i].first << "\", \"to\": \"" << edges[i].second << "\"}" << ",\n"[i==edges.size()-1];
    ss << "]}";
    return ss.str();
}


int main(){
    // vector<int> tokens = read_tokens("tokens.txt"); //���ļ�����ʷ������Ľ��
    // try {
    //     grammar_tree_node* tree = parse(g, tokens); //�﷨�����������﷨��
    //     string treejson = getTreeJson(tree);
    //     cout << treejson << '\n';
    // } catch (parse_exception e) {
    //     cout << "������" << e.row << "�е�tokenʱ��������" << e.msg << '\n';
    // }

    return 0;
}
