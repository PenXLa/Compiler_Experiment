#include <bits/stdc++.h>
using namespace std;
typedef long long LL;
string keywords[] = {"#",       "main",   "if",     "then",     "while", "do",
                     "static",  "int",    "double", "struct",   "break", "else",
                     "long",    "switch", "case",   "typedef",  "char",  "return",
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
            isend[p] = 1;  //��ǽ�β
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
    //��ѡ�����string�����ء�
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
//Ԥ����׶Σ���code׷����
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
    for (int i = 0; i < sizeof(keywords) / sizeof(string); ++i)
        tr.insert(keywords[i], i+3);  //����ؼ��ֵ�dfa.��Ϊ0~2������IDռ�ˣ�����ID��3��ʼ
    freopen("code.txt", "r", stdin); //�����ļ���code.txt
    freopen("tokens.txt", "w", stdout); //����ļ�
    string line;
    while (getline(cin, line)) append_line(line);

    vector<tuple<int, string>> tokens; //�ʷ������Ľ��
    for (int i = 0; i < code.length();) {
        if (code[i] == ' ') ++i;
        else if (isalpha(code[i])) {
            int j = i;
            for (; j <= code.length() && isalnum(code[j]); ++j);
            string word = code.substr(i, j - i);
            int node = tr.find(word);
            tokens.push_back(make_tuple(node!=-1?tr.id[node]:2, word));
            i = j;
        } else if (isdigit(code[i])) {
            int j = i;
            for (; j <= code.length() && isdigit(code[j]); ++j);
            string word = code.substr(i, j - i);
            tokens.push_back(make_tuple(3, word));
            i = j;
        } else {
            for (int j = min((int)(code.length()) - i, 2); j >= 1; --j) {
                string word = code.substr(i, j);
                int node = tr.find(word);
                if (node != -1) {
                    tokens.push_back(make_tuple(tr.id[node], word));
                    i += j;
                    goto exitsym;
                }
            }
            puts("���Ŵ���");
            return 0;
            exitsym:;
        }
    }

    for (const auto& token : tokens) 
        printf("%-4d%s\n", get<0>(token), get<1>(token).c_str());
    

    return 0;
}