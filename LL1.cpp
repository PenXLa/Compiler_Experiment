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


//语法树结点，用于储存语法树，便于查看推导过程
struct grammar_tree_node {
    int word;
    vector<grammar_tree_node*> ch;


    //输出html格式
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
    const vector<int>* tbl[200][200]; //预测分析表. tbl[i][j]表示非终结符i遇到终结符j时，应做的推导。由于非终结符是负数，所以i取相反数


    grammar(int s, initializer_list<formular> formulars): s(s) {
        for (const formular& fml : formulars) { 
            g.insert(fml);
            nter.insert(fml.A); //产生式左部加入非终结符集
            for (const auto& alpha : fml.alphas) 
                for (int word : alpha)
                    if (word < 0) nter.insert(word); //小于0，是非终结符，加入非终结符集
                    else ter.insert(word); //>=0，是终结符，加入终结符集
        }
        calc_first_set(); //预处理非终结符的first集
        calc_follow_set();//预处理非终结符的follow集
        memset(tbl, 0, sizeof tbl);
        build_table(); //构造预测分析表
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

    map<int, set<int>> fst, flw; //非终结符的first集和follow集

    //计算非终结符的first集
    void calc_first_set() {
        bool changed;
        do {
            changed = false;
            for (const formular& fml : g) { //对于每一个产生式
                for (const auto& alpha : fml.alphas) { //对于每一个候选式
                    int i = 0;
                    for (; i<alpha.size(); ++i) { //遍历候选式的每一个字
                        //下面的算法对于右部出现 左部的A 的情况是可以处理的
                        //如果出现了A，就是非终结符的情况，如果当前first(A)包含EPSLION，就可以继续处理下去
                        //如果不包含EPSLION，就退出。没有问题
                        if (alpha[i] >= 0) { //是终结符
                            changed |= set_ins(fst[fml.A], alpha[i]); //并入
                            break; //终结符first集肯定不包含空字，下面不用考虑了
                        } else { //是非终结符
                            set<int>& apfst = fst[alpha[i]]; //alpha[i]的first集
                            changed |= set_ins(fst[fml.A], apfst);
                            if (!apfst.count(EPSLION)) break; //如果first(alpha[i])不包含空字，就不必继续往下找了
                        }
                    }
                    if (i == alpha.size()) 
                        changed |= set_ins(fst[fml.A], EPSLION); //alpha===>EPSLION，那么就把EPSLION加入结果
                }
            }
        } while (changed);
    }
    //预处理非终结符的follow集
    void calc_follow_set() {
        for (int word : nter) calc_follow_set_dfs(word);
    }
    void calc_follow_set_dfs(int word) {
        if (flw.count(word)) return; //算过了，return
        if (word == s) flw[word].insert(ENDSYM); //给开始符号插结束符。本来这句写在calc_follow_set里比较好，但是这样calc_follow_set_dfs就会以为follow(s)是已经计算好的，直接跳过，所以就写这里了
        for (const auto& fml : g) { //对于每一个产生式
            for (const auto& alpha : fml.alphas) { //对于每个候选式
                bool hasEps = true; //从alpha的右边到i+1处是否可以推导出Epslion，即A->αWβ，β是否可以推导出epslion
                for (int i=alpha.size()-1; ~i; --i) { //查找word是否在候选式里
                    if (alpha[i] == word) { //找到了A->αWβ
                        set<int> betafst = first(alpha.begin()+i+1, alpha.end()); //first(β)
                        betafst.erase(EPSLION);
                        set_ins(flw[word], betafst); //follow(word) += first(β) - epslion

                        if (hasEps && fml.A != word) { //A->αWβ，β可以推导出Epslion的情况
                            calc_follow_set_dfs(fml.A); //计算follow(A)，如果算过会自动跳过
                            set_ins(flw[word], flw[fml.A]); //follow(word) += follow(A)
                        } 
                    }
                    hasEps &= first(alpha[i]).count(EPSLION); 
                }
            }
        }
    }

    const vector<int> epslionVec{EPSLION}; //一个仅包含EPSLION的vector，构造预测分析表时用
    void build_table() {
        for (const formular& fml : g) {
            set<int> aflw = follow(fml.A);
            for (const auto& alpha : fml.alphas) {
                //处理first
                set<int> apfst = first(alpha);
                for (int fstword : apfst) {
                    if (tbl[-fml.A][fstword] != nullptr) throw "Conflict when building table";
                    tbl[-fml.A][fstword] = &alpha;
                }
                //处理follow
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

//sym栈和语法树栈可以合并为1个。但是为了降低语法分析和可视化之间的耦合，分成了2个栈
grammar_tree_node* parse(const grammar& g, const vector<int>& syms) {
    stack<int> stk; //sym栈
    stk.push(ENDSYM), stk.push(g.s); //结束符和开始符

    stack<grammar_tree_node*> nodestk; //语法树栈，用于构造语法树
    grammar_tree_node* root = new grammar_tree_node; root->word = g.s; //语法树树根
    nodestk.push(nullptr), nodestk.push(root); //结点入栈

    for (int i = 0; i<syms.size();) {
        int word = stk.top(); stk.pop(); //sym出栈
        grammar_tree_node* fnode = nodestk.top(); nodestk.pop(); //语法树结点出栈
        if (word >= 0) { //是终结符
            if (word != syms[i]) puts("ERR1"), throw "ERROR";
            ++i;
        } else { //是非终结符
            const vector<int>* nxt = g.tbl[-word][syms[i]]; //预测分析表内容
            if (nxt == nullptr) 
                puts("ERR2"), throw "ERROR";
            for (auto it = nxt->crbegin(); it != nxt->crend(); ++it) //产生式倒序入栈
                if (*it != EPSLION) stk.push(*it);

            //语法树子节点
            int inx = nxt->size(); 
            fnode->ch.resize(inx);
            for (auto it = nxt->crbegin(); it != nxt->crend(); ++it) {
                grammar_tree_node* nd = new grammar_tree_node; 
                nd->word = *it;
                fnode->ch[--inx] = nd; //在倒序遍历中插入正序的子节点
                if (*it != EPSLION) nodestk.push(nd);
            }
        }
    }
    return root;
}



//************↓文法定义*******************
//为了编码方便，把数字sym弄成enum。不要用0和1，防止和EPSLION和ENDSYM的值相同。
enum words {
//终结符
ADD = 2,    MUL = 3,    LB = 4,
RB  = 5,    I   = 6,
//非终结符
E   = -1,   E1  = -2,   T = -3,
T1  = -4,   F   = -5,
};
//产生式
grammar g(E, {
    formular(E,     {{T, E1}}),
    formular(E1,    {{ADD, T, E1}, {EPSLION}}),
    formular(T,     {{F, T1}}),
    formular(T1,    {{MUL, F, T1}, {EPSLION}}),
    formular(F,     {{LB, E, RB}, {I}})
});
//************↑文法定义*******************

int main(){
    vector<int> syms{I, ADD, I, ENDSYM}; 
    grammar_tree_node* tree = parse(g, syms); 

    //输出语法树到HTML
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
写计算first集的代码时，发现了一个问题。
求first集时，有first(X)依赖于first(Y)的情况
比如A->Bc
这时first(B)就要并入first(A)中。
但是并入时，first(B)可能并没有完全算出，所以课本采用了不断地循环来求first集的方法，直到结果不再改变为止。

但是老师给的word文档中，似乎采用了递归计算的方法，要把first(B)并入first(A)时，直接递归计算first(B)，
保证first(B)完全计算时，再并入first(A)。

这样似乎不需要一直循环了。可是仔细一想，这样似乎也不对。
首先我考虑到了A->Ab|...的情况，first(A)依赖于first(A)。
这时要怎么处理呢？如果在最终的结果中，first(A)包含epslion，那么first(A)就可以把b也并进来。
反之则不可以。但是我们现在是无法知道first(A)最终是否会包含epslion。
所以这种递归的方法是不可行的。
另外，我也不确定这种递归是否存在环形调用，如果存在，那就是死递归了。

但是我还没对该问题进行建模，只是有一个感性的认识。有时间可以总结建模一下。
*/