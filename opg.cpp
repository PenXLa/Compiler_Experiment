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


//语法树结点，用于储存语法树，便于查看推导过程
struct grammar_tree_node {
    int word;
    vector<grammar_tree_node*> ch;
    ~grammar_tree_node() {
        for (grammar_tree_node* nd : ch) delete nd;
    }
};

enum pre_def_words {EPSLION = 0, ENDSYM = 1}; //结束符和空字。几乎所有的文法都需要这两个字符，所以定义到了这里。
//产生式的终结符和非终结符均用int表示。
//负数是非终结符，非负数是终结符，也就是词法分析阶段得到的sym
//产生式，A->α1|α2...
struct formular {
    int A;
    vector<vector<int>> alphas; //一个vector<int>表示了一个候选式，再套一个vector就是候选式集合

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
    set<int> nter, ter; //非终结符和终结符
    int s; //开始符号
    char tbl[200][200]; //优先关系表,'<'表示<，'='表示=，'>'表示>，0表示未定义


    grammar(int s, initializer_list<formular> formulars): s(s) {
        for (const formular& fml : formulars) { 
            g.insert(fml);
            nter.insert(fml.A); //产生式左部加入非终结符集
            for (const auto& alpha : fml.alphas) 
                for (int word : alpha)
                    if (word < 0) nter.insert(word); //小于0，是非终结符，加入非终结符集
                    else ter.insert(word); //>=0，是终结符，加入终结符集
        }
        calc_firstvt(); //预处理非终结符的first集
        calc_lastvt();//预处理非终结符的follow集
        memset(tbl, 0, sizeof tbl);
        build_table(); //构造预测分析表
        build_reduceVN();
    }
//private:
    //往set1中插入x，返回插入后set1是否改变
    bool set_ins(set<int>& set1, int x) {
        if (set1.count(x)) return false;
        set1.insert(x);
        return true;
    }
    //往set1中插入set2，返回插入后set1是否改变
    bool set_ins(set<int>& set1, const set<int>& set2) {
        if (includes(set1.cbegin(), set1.cend(), set2.cbegin(), set2.cend())) return false;
        set1.insert(set2.begin(), set2.end());
        return true;
    }

    map<int, set<int>> fst, lst; //非终结符的firstvt和lastvt

    //计算非终结符的firstvt
    void calc_firstvt() {
        bool changed = false;
        do {
            changed = false;
            for (const formular& fml : g) { //遍历产生式
                for (const auto& alpha : fml.alphas) { //遍历候选式
                    if (alpha[0]>=0) changed |= set_ins(fst[fml.A], alpha[0]); //P->a的情况
                    else {
                        changed |= set_ins(fst[fml.A], fst[alpha[0]]); //P->Q的情况
                        if (alpha.size() > 1) changed |= set_ins(fst[fml.A], alpha[1]);//如果存在第二个字符，根据算符优先文法定义，必定是非终结符
                    }
                }
            }
        } while (changed);
    }
    //预处理非终结符的lastvt
    void calc_lastvt() {
        bool changed = false;
        do {
            changed = false;
            for (const formular& fml : g) { //遍历产生式
                for (const auto& alpha : fml.alphas) { //遍历候选式
                    if (alpha.back()>0) changed |= set_ins(lst[fml.A], alpha.back()); //P->...a的情况
                    else {
                        changed |= set_ins(lst[fml.A], lst[alpha.back()]); //P->...Q的情况
                        if (alpha.size() > 1) changed |= set_ins(lst[fml.A], alpha[alpha.size()-2]);//如果存在第二个字符，根据算符优先文法定义，必定是非终结符
                    }
                }
            }
        } while (changed);
    }
    

    void build_table() {
        for (const formular& fml : g) { //遍历产生式
            for (const auto& alpha : fml.alphas) { //遍历候选式
                for (int i=1; i<alpha.size()-1; ++i) //查找aQb的情况
                    if (alpha[i]<0 && alpha[i-1]>=0 && alpha[i+1]>=0) 
                        tbl[alpha[i-1]][alpha[i+1]] = '=';
                for (int i=1; i<alpha.size(); ++i) { //查找ab、aQ、Qb
                    if (alpha[i]<0 && alpha[i-1]<0) 
                        tbl[alpha[i-1]][alpha[i]] = '='; //ab
                    else if (alpha[i-1]>=0 && alpha[i]<0)  //aQ
                        for (int vt : fst[alpha[i]]) 
                            tbl[alpha[i-1]][vt] = '<';
                    else if (alpha[i-1]<0 && alpha[i]>=0)  //Qb
                        for (int vt : lst[alpha[i-1]]) 
                            tbl[vt][alpha[i]]= '>';
                    else throw "Error";//出现了连续的非终结符
                }
            }
        }
    }

    map<vector<int>, int> reduceVN; //算符优先文法的规约表，为了方便parse函数使用，key是stack，倒序的
    void build_reduceVN() { 
        for (const formular& fml : g) { //遍历产生式
            for (const auto& alpha : fml.alphas) { //遍历候选式
                vector<int> alphavt;
                for (int i=alpha.size(); i>=0; --i) if (alpha[i]>=0) 
                    alphavt.push_back(alpha[i]);
                reduceVN[alphavt] = fml.A;
            }
        }
    }
};

//读取词法分析的结果
//仅读取token的id，不读取实际内容
vector<int> read_tokens(string file) {
    vector<int> tokens;
    int id; string word;
    ifstream fin("tokens.txt");
    while(fin >> id >> word) {
        tokens.push_back(id);
    }
    fin.close();
    tokens.push_back(ENDSYM); //追加一个结束符
    return tokens;
}


//************↓文法定义*******************
//为了编码方便，把数字sym弄成enum。不要用0和1，防止和EPSLION和ENDSYM的值相同。
enum words {
//终结符
ADD = 2,    MUL = 3,    LB = 4,
RB  = 5,    I   = 6,
//非终结符
E   = -1,   E1  = -2,   T = -3,     F   = -5,
};
//产生式
grammar g(E1, {
    formular(E1,     {{ENDSYM, E, ENDSYM}}),
    formular(E,     {{E, ADD, T}, {T}}),
    formular(T,     {{T, MUL, F}, {F}}),
    formular(F,     {{LB, E, RB}, {I}})
});
map<int, string> id2name = {
    {E, "E"}, {T, "T"}, {F, "F"}, 
    {I, "i"}, {ADD, "+"}, {MUL, "*"}, {LB, "("}, {RB, ")"}, {EPSLION, "ε"}, {ENDSYM, "#"}
}; //用于把文法字符的ID转换成便于观察的符号，作用仅仅是便于观察计算结果，对算法本身没有影响。
//************↑文法定义*******************



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
//sym栈和语法树栈可以合并为1个。但是为了降低语法分析和可视化之间的耦合，分成了2个栈
void parse(grammar& g, const vector<int>& syms) {
    printf("%-16s%-16s%-10s\n%-16s%", "Stack", "input", "Action", "#");
    for (int word : syms) cout << id2name[word]; 
    for (int j=0; j<16-syms.size(); ++j) cout << ' '; cout << "Prepare\n";


    vector<int> stk, prime; //符号栈和素短语临时栈.由于算符优先文法忽略非终结符的作用，所以符号栈可以不再加入非终结符。
    stk.push_back(ENDSYM);
    for (int i=0; i<syms.size(); ++i) {
        while (g.tbl[getTopVT(stk)][syms[i]] == '>') {
            vector<int> poplist; //出栈的符号，用于输出过程
            do {
                if (stk.back() < 0) poplist.push_back(stk.back()), stk.pop_back(); 
                poplist.push_back(stk.back());
                prime.push_back(stk.back()); 
                stk.pop_back();
            } while(g.tbl[getTopVT(stk)][prime.back()] == '=');
            if (stk.back() < 0) poplist.push_back(stk.back()), stk.pop_back(); //读入最后一个非终结符

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
    vector<int> tokens = read_tokens("tokens.txt"); //从文件读入词法分析的结果
    prtOPTable(g);

    parse(g, tokens); //语法分析

    system("pause");
    return 0;
}
