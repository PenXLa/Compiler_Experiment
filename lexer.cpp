#include <bits/stdc++.h>
using namespace std;
typedef long long LL;
string tokens[] = {"#",       "main",   "if",     "then",     "while", "do",
                   "static",  "int",    "double", "struct",   "break", "else",
                   "long",    "switch", "case",   " typedef", "char",  "return",
                   "const",   "float",  "short",  "continue", "for",   "void",
                   "default", "sizeof", "+",      "-",        "*",     "/",
                   ":",       ":=",     "<",      "<>",       "<=",    ">",
                   ">=",      "=",      ";",      "(",        ")",     "{", 
                   "}",       ","};

struct trie {
    static const int charsetn = 128;
    int cnt = 0;
    static const int noden = 1000;
    int nex[noden][charsetn];
    int isend[noden];
    int id[noden];
    void insert(const char* begin, const char* end, int nodeid) {
        int p = 0;
        for (const char* c = begin; c != end; ++c) {
            int ci = *c;
            if (!nex[p][ci]) nex[p][ci] = ++cnt;
            p = nex[p][ci];
            isend[p] = 1;  //标记结尾
            id[p] = nodeid;
        }
    }
    int find(const char* begin, const char* end) {
        int p = 0;
        for (const char* c = begin; c != end; ++c) {
            int ci = *c;
            if (!nex[p][ci]) return -1;
            p = nex[p][ci];
        }
        return isend[p] ? p : -1;
    }
    //可选，针对string的重载↓
    void insert(const string& str, int id) {
        const char* cs = str.c_str();
        insert(cs, cs + str.length(), id);
    }

    int find(const string& str) {
        const char* cs = str.c_str();
        return find(cs, cs + str.length());
    }
};

string code;
//预处理阶段，给code追加行
void append_line(const string& line) {
    bool last_is_space = false;
    char lastc = 0;
    for (char c : line) {
        if (c == '/' && lastc == '/') {
            code.pop_back();
            return;
        }
        if (c != '\n' && c != '\r') {
            if (c == '\t' || c == ' ') {
                if (!last_is_space) {
                    code.push_back(' ');
                    last_is_space = 1;
                }
            } else {
                code.push_back(c);
                last_is_space = 0;
            }
        }
        lastc = c;
    }
}

trie tr;
int main() {
    for (int i = 0; i < sizeof(tokens) / sizeof(string); ++i)
        tr.insert(tokens[i], i+3);  //构造关键字的dfa.因为0~2被特殊ID占了，所以ID从3开始
    freopen("code.txt", "r", stdin); //输入文件是code.txt
    freopen("out.txt", "w", stdout); //输出文件是out.txt
    string line;
    while (getline(cin, line)) append_line(line);
    for (int i = 0; i < code.length();) {
        if (code[i] == ' ') ++i;
        else if (isalpha(code[i])) {
            int j = i;
            for (; j <= code.length() && isalnum(code[j]); ++j);
            string word = code.substr(i, j - i);
            printf("<%-6s,", word.c_str());
            int node = tr.find(word);
            if (node != -1) cout << tr.id[node] << ">\n";
            else cout << "2>\n";
            i = j;
        } else if (isdigit(code[i])) {
            int j = i;
            for (; j <= code.length() && isdigit(code[j]); ++j);
            string word = code.substr(i, j - i);
            printf("<%-6s,3>\n", word.c_str());
            i = j;
        } else {
            for (int j = min((int)(code.length()) - i, 2); j >= 1; --j) {
                string word = code.substr(i, j);
                int node = tr.find(word);
                if (node != -1) {
                    printf("<%-6s,%d>\n", word.c_str(), tr.id[node]);
                    i += j;
                    goto exitsym;
                }
            }
            puts("符号错误");
            return 0;
            exitsym:;
        }
    }
    return 0;
}