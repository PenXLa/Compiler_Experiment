#include <set>
#include <iostream>
#include <vector>
#include <map>
#include <algorithm>
#include <iterator>
#include <cstring>
#include <stack>
#include<fstream>
using namespace std;
typedef long long LL;


//�﷨����㣬���ڴ����﷨�������ڲ鿴�Ƶ�����
struct grammar_tree_node {
    int word;
    vector<grammar_tree_node*> ch;


    //���html��ʽ
    void output(ostream& out) {
        if (ch.empty()) {
            out << "<li>" << word << "</li>\n";
        } else {
            out << "<li><span class='caret'>" << word << "</span><ul class='nested'>\n";
            for (grammar_tree_node* nd : ch) nd->output(out);
            out << "</ul></li>\n";
        }
    }

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
    const vector<int>* tbl[200][200]; //Ԥ�������. tbl[i][j]��ʾ���ս��i�����ս��jʱ��Ӧ�����Ƶ������ڷ��ս���Ǹ���������iȡ�෴��


    grammar(int s, initializer_list<formular> formulars): s(s) {
        for (const formular& fml : formulars) { 
            g.insert(fml);
            nter.insert(fml.A); //����ʽ�󲿼�����ս����
            for (const auto& alpha : fml.alphas) 
                for (int word : alpha)
                    if (word < 0) nter.insert(word); //С��0���Ƿ��ս����������ս����
                    else ter.insert(word); //>=0�����ս���������ս����
        }
        calc_first_set(); //Ԥ������ս����first��
        calc_follow_set();//Ԥ������ս����follow��
        memset(tbl, 0, sizeof tbl);
        build_table(); //����Ԥ�������
    }
    

    set<int> first(int word) {
        if (word < 0) return fst[word];
        return set<int>({word});
    }
    set<int> first(const vector<int>& alpha) {
        set<int> ret;
        for (int word : alpha) {
            if (word >= 0) {
                ret.insert(word);
                return ret;
            } else {
                set<int>& tmp = fst[word];
                set_ins(ret, tmp);
                if (!tmp.count(EPSLION)) return ret;
            }
        }
        ret.insert(EPSLION);
        return ret;
    }
    set<int> first(vector<int>::const_iterator beg, vector<int>::const_iterator end) {
        set<int> ret;
        for (auto p = beg; p != end; ++p) {
            if (*p >= 0) {
                ret.insert(*p);
                return ret;
            } else {
                set<int>& tmp = fst[*p];
                set_ins(ret, tmp);
                if (!tmp.count(EPSLION)) return ret;
            }
        }
        ret.insert(EPSLION);
        return ret;
    }

    set<int> follow(int word) {
        if (word < 0) return flw[word];
        throw "error in follow";
    }
private:
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

    map<int, set<int>> fst, flw; //���ս����first����follow��

    //������ս����first��
    void calc_first_set() {
        bool changed;
        do {
            changed = false;
            for (const formular& fml : g) { //����ÿһ������ʽ
                for (const auto& alpha : fml.alphas) { //����ÿһ����ѡʽ
                    int i = 0;
                    for (; i<alpha.size(); ++i) { //������ѡʽ��ÿһ����
                        //������㷨�����Ҳ����� �󲿵�A ������ǿ��Դ����
                        //���������A�����Ƿ��ս��������������ǰfirst(A)����EPSLION���Ϳ��Լ���������ȥ
                        //���������EPSLION�����˳���û������
                        if (alpha[i] >= 0) { //���ս��
                            changed |= set_ins(fst[fml.A], alpha[i]); //����
                            break; //�ս��first���϶����������֣����治�ÿ�����
                        } else { //�Ƿ��ս��
                            set<int>& apfst = fst[alpha[i]]; //alpha[i]��first��
                            changed |= set_ins(fst[fml.A], apfst);
                            if (!apfst.count(EPSLION)) break; //���first(alpha[i])���������֣��Ͳ��ؼ�����������
                        }
                    }
                    if (i == alpha.size()) 
                        changed |= set_ins(fst[fml.A], EPSLION); //alpha===>EPSLION����ô�Ͱ�EPSLION������
                }
            }
        } while (changed);
    }
    //Ԥ������ս����follow��
    void calc_follow_set() {
        for (int word : nter) calc_follow_set_dfs(word);
    }
    void calc_follow_set_dfs(int word) {
        if (flw.count(word)) return; //����ˣ�return
        if (word == s) flw[word].insert(ENDSYM); //����ʼ���Ų���������������д��calc_follow_set��ȽϺã���������calc_follow_set_dfs�ͻ���Ϊfollow(s)���Ѿ�����õģ�ֱ�����������Ծ�д������
        for (const auto& fml : g) { //����ÿһ������ʽ
            for (const auto& alpha : fml.alphas) { //����ÿ����ѡʽ
                bool hasEps = true; //��alpha���ұߵ�i+1���Ƿ�����Ƶ���Epslion����A->��W�£����Ƿ�����Ƶ���epslion
                for (int i=alpha.size()-1; ~i; --i) { //����word�Ƿ��ں�ѡʽ��
                    if (alpha[i] == word) { //�ҵ���A->��W��
                        set<int> betafst = first(alpha.begin()+i+1, alpha.end()); //first(��)
                        betafst.erase(EPSLION);
                        set_ins(flw[word], betafst); //follow(word) += first(��) - epslion

                        if (hasEps && fml.A != word) { //A->��W�£��¿����Ƶ���Epslion�����
                            calc_follow_set_dfs(fml.A); //����follow(A)�����������Զ�����
                            set_ins(flw[word], flw[fml.A]); //follow(word) += follow(A)
                        } 
                    }
                    hasEps &= first(alpha[i]).count(EPSLION); 
                }
            }
        }
    }

    const vector<int> epslionVec{EPSLION}; //һ��������EPSLION��vector������Ԥ�������ʱ��
    void build_table() {
        for (const formular& fml : g) {
            set<int> aflw = follow(fml.A);
            for (const auto& alpha : fml.alphas) {
                //����first
                set<int> apfst = first(alpha);
                for (int fstword : apfst) {
                    if (tbl[-fml.A][fstword] != nullptr) throw "Conflict when building table";
                    tbl[-fml.A][fstword] = &alpha;
                }
                //����follow
                if (apfst.count(EPSLION)) {
                    for (int flwword : aflw) {
                        if (tbl[-fml.A][flwword] != nullptr) throw "Conflict when building table";
                        tbl[-fml.A][flwword] = &epslionVec;
                    }
                }
            }
        }
    }
    
};

//symջ���﷨��ջ���Ժϲ�Ϊ1��������Ϊ�˽����﷨�����Ϳ��ӻ�֮�����ϣ��ֳ���2��ջ
grammar_tree_node* parse(const grammar& g, const vector<int>& syms) {
    stack<int> stk; //symջ
    stk.push(ENDSYM), stk.push(g.s); //�������Ϳ�ʼ��

    stack<grammar_tree_node*> nodestk; //�﷨��ջ�����ڹ����﷨��
    grammar_tree_node* root = new grammar_tree_node; root->word = g.s; //�﷨������
    nodestk.push(nullptr), nodestk.push(root); //�����ջ

    for (int i = 0; i<syms.size();) {
        int word = stk.top(); stk.pop(); //sym��ջ
        grammar_tree_node* fnode = nodestk.top(); nodestk.pop(); //�﷨������ջ
        if (word >= 0) { //���ս��
            if (word != syms[i]) puts("ERR1"), throw "ERROR";
            ++i;
        } else { //�Ƿ��ս��
            const vector<int>* nxt = g.tbl[-word][syms[i]]; //Ԥ�����������
            if (nxt == nullptr) 
                puts("ERR2"), throw "ERROR";
            for (auto it = nxt->crbegin(); it != nxt->crend(); ++it) //����ʽ������ջ
                if (*it != EPSLION) stk.push(*it);

            //�﷨���ӽڵ�
            int inx = nxt->size(); 
            fnode->ch.resize(inx);
            for (auto it = nxt->crbegin(); it != nxt->crend(); ++it) {
                grammar_tree_node* nd = new grammar_tree_node; 
                nd->word = *it;
                fnode->ch[--inx] = nd; //�ڵ�������в���������ӽڵ�
                if (*it != EPSLION) nodestk.push(nd);
            }
        }
    }
    return root;
}



//************���ķ�����*******************
//Ϊ�˱��뷽�㣬������symŪ��enum����Ҫ��0��1����ֹ��EPSLION��ENDSYM��ֵ��ͬ��
enum words {
//�ս��
ADD = 2,    MUL = 3,    LB = 4,
RB  = 5,    I   = 6,
//���ս��
E   = -1,   E1  = -2,   T = -3,
T1  = -4,   F   = -5,
};
//����ʽ
grammar g(E, {
    formular(E,     {{T, E1}}),
    formular(E1,    {{ADD, T, E1}, {EPSLION}}),
    formular(T,     {{F, T1}}),
    formular(T1,    {{MUL, F, T1}, {EPSLION}}),
    formular(F,     {{LB, E, RB}, {I}})
});
//************���ķ�����*******************

int main(){
    vector<int> syms{I, ADD, I, ENDSYM}; 
    grammar_tree_node* tree = parse(g, syms); 

    //����﷨����HTML
    ofstream fout("grammar tree.html");
    fout << "<html><head><style>\n" <<
        "ul,#myUL{list-style-type:none;}#myUL{margin:0;padding:0;}\n" <<
        ".caret{cursor:pointer;-webkit-user-select:none;\n" << 
        "-moz-user-select: none;-ms-user-select:none;user-select:none;}\n" <<
        ".caret::before {content:'\\25B6';color:black;\n" <<
        "display:inline-block;margin-right:6px;}\n" <<
        ".caret-down::before{-ms-transform:rotate(90deg);\n" <<
        "-webkit-transform:rotate(90deg);transform:rotate(90deg);}\n" <<
        ".nested{display:none;}.active{display: block;}\n" <<
        "</style></head><body><ul id='myUL'>\n";
    tree->output(fout);
    fout << "<script>\n" <<
            "var toggler=document.getElementsByClassName('caret');\n" <<
            "var i;for (i=0;i<toggler.length;i++){\n" <<
            "toggler[i].addEventListener('click',function(){\n" <<
            "this.parentElement.querySelector('.nested').classList.toggle('active');\n" <<
            "this.classList.toggle('caret-down');\n" <<
            "});}</script></ul></body></html>\n";
    fout.close();
    return 0;
}


/*
д����first���Ĵ���ʱ��������һ�����⡣
��first��ʱ����first(X)������first(Y)�����
����A->Bc
��ʱfirst(B)��Ҫ����first(A)�С�
���ǲ���ʱ��first(B)���ܲ�û����ȫ��������Կα������˲��ϵ�ѭ������first���ķ�����ֱ��������ٸı�Ϊֹ��

������ʦ����word�ĵ��У��ƺ������˵ݹ����ķ�����Ҫ��first(B)����first(A)ʱ��ֱ�ӵݹ����first(B)��
��֤first(B)��ȫ����ʱ���ٲ���first(A)��

�����ƺ�����Ҫһֱѭ���ˡ�������ϸһ�룬�����ƺ�Ҳ���ԡ�
�����ҿ��ǵ���A->Ab|...�������first(A)������first(A)��
��ʱҪ��ô�����أ���������յĽ���У�first(A)����epslion����ôfirst(A)�Ϳ��԰�bҲ��������
��֮�򲻿��ԡ����������������޷�֪��first(A)�����Ƿ�����epslion��
�������ֵݹ�ķ����ǲ����еġ�
���⣬��Ҳ��ȷ�����ֵݹ��Ƿ���ڻ��ε��ã�������ڣ��Ǿ������ݹ��ˡ�

�����һ�û�Ը�������н�ģ��ֻ����һ�����Ե���ʶ����ʱ������ܽὨģһ�¡�
*/