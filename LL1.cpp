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


struct parse_exception : public exception {
    int row;
    string msg;
    parse_exception(int row, const string& msg): row(row), msg(msg) { }
    const char* what() const throw() { return ""; }
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
            if (word != syms[i]) {
                stringstream ss;
                ss << "遇到错误符号。期望是[" << word << "]，但遇到了[" << syms[i] << "]"; 
                throw parse_exception(i+1, ss.str());
            }
            ++i;
        } else { //是非终结符
            const vector<int>* nxt = g.tbl[-word][syms[i]]; //预测分析表内容
            if (nxt == nullptr) {
                stringstream ss;
                ss << "遇到了非期望的符号[" << syms[i] << ']'; 
                throw parse_exception(i+1, ss.str());
            }
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
        ss << "{ \"id\": \"" << nodes[i] << "\",\"label\": \"" << nodes[i]->word << "\" }" << ",\n"[i==nodes.size()-1];
    ss << "],\"edges\": [";
    for (int i=0; i<edges.size(); ++i) 
        ss << "{ \"from\": \"" << edges[i].first << "\", \"to\": \"" << edges[i].second << "\"}" << ",\n"[i==edges.size()-1];
    ss << "]}";
    return ss.str();
}


int main(){
    vector<int> tokens = read_tokens("tokens.txt"); //从文件读入词法分析的结果
    try {
        grammar_tree_node* tree = parse(g, tokens); //语法分析，生成语法树
        string treejson = getTreeJson(tree);
        cout << treejson << '\n';
    } catch (parse_exception e) {
        cout << "解析第" << e.row << "行的token时遇到错误：" << e.msg << '\n';
    }

    
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

/*
类C语言文法的设计
带中括号的是非终结符，用空格分隔各个符号
[Program] -> [DeclarationList]  //程序由定义列表组成
[DeclarationList] -> [Declaration] [DeclarationList] | epslion //定义表由多条定义组成
[Declaration] -> [VarDec] | [FunDec]  //定义由变量定义和函数定义组成

[Const] -> const | epslion // 可选的const关键字
[Static] -> static | epslion // 可选的static关键字
[VarDec] -> [GlobalVarDec] | [ScopedVarDec] //变量定义有全局和局部（局部可以带static）
[GlobalVarDec] -> [Const] [TypeSpecifier] [VarDecList] semicolon //全局变量定义由类型限定符和变量列表以及分号组成
[ScopedVarDec] -> [Static] [GlobalVarDec] semicolon
[TypeSpecifier] -> int | float | double | long | bool | char | ID //类型标识符
[VarDecList] -> [VarDecInit], [VarDecList] | [VarDecInit] //变量声明列表由变量初始化组成
[VarDecInit] -> [SimpleVarDecInit] | [ArrayDecInit] | [PointerDecInit] //形如 a、a=2、a[2]、a[2]={1,2}、*a、*a=b等
[SimpleVarDecInit] -> ID [SimpleVarAssignment] //普通变量初始化
[SimpleVarAssignment] -> = [Expression] | epslion //普通变量赋值
[ArrayDecInit] -> ID [ArrayDim] [ArrayAssignment] //表达式列表
[ArrayDim] -> [ [ArrayLen] ][ArrayDim] | [ [ArrayLen] ]  //数组维数，真的有中括号
[ArrayAssignment] -> = { [ExpressionList] } | epslion  //数组赋值
[ArrayLen] -> [NUM] | epslion //数组长度可以为常数，也可以为空
[PointerDecInit] -> [PointerStars] ID [PointerVarAssignment]
[PointerStars] -> *[PointerStars] | *
[PointerVarAssignment] -> = [Expression] | epslion //指针变量赋值

[ReturnType] -> void | [TypeSpecifier] //函数返回值可以用void
[FunDec] -> [ReturnType] ID ([Params]) [Statement] //函数定义
[Params] -> [ParamList] | epslion
[ParamList] -> [ParamDec], [ParamList] | [ParamDec] //把参数列表分为Params和ParamList是有必要的。它避免了分隔逗号的多余
[ParamDec] -> [TypeSpecifier] [VarDecInit]

[Sentence] -> [ExpSt] | [DecSt] | [IfSt] | [ForSt] | [WhileSt] | [DoSt] | [BreakSt] | [ContinueSt] | [ReturnSt]
[ExpSt] -> [Expression] semicolon | semicolon  //表达式语句
[DecSt] -> [ScopedVarDec]  //局部声明语句
[IfSt] -> if ( [Expression] ) [Statement] [ElseSt] //If语句
[ElseSt] -> else [Statement] | epslion // else语句
[ForSt] -> for ( [ForInit] [ExpSt] [ExpSt] ) [Statement]
[ForInit] -> [DecSt] | [ExpSt]
[WhileSt] -> while ( [Expression] ) [Statement]
[DoSt] -> do [Statement] while ( [Expression] ) semicolon
[BreakSt] -> break semicolon
[ContinueSt] -> continue semicolon
[ReturnSt] -> return [NullableExp] semicolon


[ExpEle] -> ID | NUM | ( [Expression] )  //表达式的基本元素为ID或NUM或带括号的Expression
//1级运算符，包括数组下标、函数后面的参数表、数据成员、后置++和--，都是左结合
[Exp1] -> [ArrInxExp] | [FunParamExp] | [MemberExp] | [PointerMemberExp] | [IncExpA] | [DecExpA]
[ArrInxExp] -> [ExpEle] [ [Expression] ]
[FunParamExp] -> [ExpEle] ( [ExpressionList] )
[MemberExp] -> [ExpEle] . ID
[PointerMemberExp] -> [ExpEle] -> ID
[IncExpA] -> [ExpEle] ++
[DecExpA] -> [ExpEle] --

//二级运算符，包括负号、强制类型转换、前置++ -- 取值* 取址& ! ~ sizeof
[Exp2] -> [NegExp] | [CastExp] | [IncExpB] | [DecExpB] | [PtrStarExp] | [AddrExp] | [NotExp] | [SizeofExp]
[NegExp] -> - [Exp1]
[CastExp] -> ( [TypeSpecifier] ) [Exp1]
[IncExpB] -> [Exp1] ++
[DecExpB] -> [Exp1] --
[PtrStarExp] -> * [Exp1]
[AddrExp] -> & [Exp1]



[Expression] -> [Exp14] [Expression']
[Expression'] -> , [Exp14] [Expression'] | epslion
//14级运算符，包括 =  /=  *=  %=  +=  -=  <<=  >>=  &=  ^=  |=，都是右结合
//这里的运算符的共同特点是，会给左边赋值，所以运算符左边必须是变量。
[Exp14] -> [ID] [Exp14Ops] | [Exp13] //最终格式为ID=ID/=ID*=ID=ID%=...=ID=Exp13
[Exp14Ops] -> [AsmtExp] | [DivAsmtExp] | [MulAsmtExp] | [ModAsmtExp] | [AddAsmtExp] | [SubAsmtExp] | [LSAsmtExp] | [RSAsmtExp] | [AndAsmtExp] | [XorAsmtExp] | [OrAsmtExp]
[AsmtExp] -> = [Exp14]
[DivAsmtExp] -> /= [Exp14]
[MulAsmtExp] -> *= [Exp14]
[ModAsmtExp] -> %= [Exp14]
[AddAsmtExp] -> += [Exp14]
[SubAsmtExp] -> -= [Exp14]
[LSAsmtExp] -> <<= [Exp14]
[RSAsmtExp] -> >>= [Exp14]
[AndAsmtExp] -> &= [Exp14]
[XorAsmtExp] -> ^= [Exp14]
[OrAsmtExp] -> |= [Exp14]
//13级运算符，仅包括条件运算符（待改）
[Exp13] -> [Exp12] [Exp13']
[Exp13'] -> ? [Exp13] : [Exp13] [Exp13'] //这个是为了消除左递归
//12级运算符，仅包括||，左结合
[Exp12] -> [Exp11] [Exp12']
[Exp12'] -> || [Exp11] [Exp12'] | epslion //为了消除左递归
//11级运算符，仅包括&&
[Exp11] -> [Exp10] [Exp11']
[Exp11'] -> && [Exp10] [Exp11'] | epslion 
//10级运算符，仅包括 |
[Exp10] -> [Exp19] [Exp10']
[Exp10'] -> | [Exp9] [Exp10'] | epslion //第一个|是or，而不是分割号
//9级运算符，仅包括 ^
[Exp9] -> [Exp8] [Exp9']
[Exp9'] -> ^ [Exp8] [Exp9'] | epslion 
//8级运算符，仅包括 &
[Exp8] -> [Exp7] [Exp8']
[Exp8'] -> & [Exp7] [Exp8'] | epslion 
//7级运算符，包括!=和==，

[Expression] -> [SimpleExpression] , [Expression] | [SimpleExpression]
[ExpressionList] -> [Expression]
*/