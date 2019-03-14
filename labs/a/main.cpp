#include <iostream>
#include <algorithm>
#include <vector>
#include <regex>

enum token {
    OPEN, CLOSE, VAR, AND, OR, IMPL, NOT, END
};

class ParsingTreeBuilder {
public:
    ParsingTreeBuilder(const std::string &expression) {
        this->expression = expression;
        pointer = 0;
        vars.emplace_back("&");
        vars.emplace_back("|");
        vars.emplace_back("->");
        vars.emplace_back("!");
    }

    void parse() {
        root = std::move(impl());
        print(root);
    }

private:
    struct Node;
    typedef std::unique_ptr<Node> pNode;

    struct Node {
        Node(size_t val) : value(val), left(nullptr), right(nullptr) {}

        Node(size_t val, pNode l, pNode r) {
            value = val;
            left = std::move(l);
            right = std::move(r);
        }

        size_t value;
        pNode left, right;
    };

    bool partOfName(char c) {
        return ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '\'';
    }

    void print(const pNode &node) const {
        if (node == nullptr) {
            return;
        }

        if (node->left != nullptr)
            std::cout << "(";

        std::cout << vars[node->value];

        if (node->left != nullptr && node->right != nullptr)
            std::cout << ",";

        print(node->left);

        if (node->left != nullptr && node->right != nullptr)
            std::cout << ",";

        print(node->right);

        if (node->left != nullptr)
            std::cout << ")";
    }

    // returns length of variable name and move pointer to the index of last letter in variable name
    size_t get_variable_name_len() {
        size_t start = 0;
        while (pointer < expression.length() && partOfName(expression[pointer])) {
            ++pointer;
            ++start;
        }
        return start;
    }

    void skip_spaces() {
        while (pointer < expression.length() && expression[pointer] == ' ') {
            ++pointer;
        }
    }

    void get_token() {
        skip_spaces();
        if (pointer >= expression.length()) {
            cur_token = END;
            return;
        }

        char cur_symbol = expression[pointer];

        switch (cur_symbol) {
            case '-' : {
                ++pointer;
                cur_token = IMPL;
                break;
            }
            case '&' : {
                cur_token = AND;
                break;
            }
            case '|' : {
                cur_token = OR;
                break;
            }
            case '!' : {
                cur_token = NOT;
                break;
            }
            case '(' : {
                cur_token = OPEN;
                break;
            }
            case ')' : {
                cur_token = CLOSE;
                break;
            }
            default: {
                cur_token = VAR;
                size_t start = pointer;
                cur_var_name = expression.substr(start, get_variable_name_len());
                --pointer;
                break;
            }
        }
        ++pointer;
    }

    pNode ver() {
        get_token();
        pNode result;

        switch (cur_token) {
            case VAR : {
                vars.push_back(cur_var_name);
                result.reset(new Node(vars.size() - 1));
                get_token();
                break;
            }
            case NOT : {
                pNode tmp(new Node(3, std::move(ver()), nullptr));
                result = std::move(tmp);
                //  result = "(!" + ver() + ")";
                break;
            }
            case OPEN : {
                result = std::move(impl());
                //    result = "(" + impl() + ")";
                get_token();
                break;
            }
        }
        return result;
    }


    pNode conj() {
        pNode result = ver();
        while (true) {
            switch (cur_token) {
                case AND: {
                    //result = "(&, " + result + ", " + ver() + ")";
                    pNode tmp(new Node(0, std::move(result), std::move(ver())));
                    result = std::move(tmp);
                    break;
                }
                default:
                    return result;
            }
        }
    }

    pNode disj() {
        pNode result = conj();
        while (true) {
            switch (cur_token) {
                case OR : {
                    //      result = "(|, " + result + ", " + conj() + ")";
                    pNode tmp(new Node(1, std::move(result), std::move(conj())));
                    result = std::move(tmp);
                    break;
                }
                default:
                    return result;
            }
        }
    }

    pNode impl() {
        pNode result = disj();
        while (true) {
            switch (cur_token) {
                case IMPL : {
                    //result = "(->, " + result + ", " + impl() + ")";
                    pNode tmp(new Node(2, std::move(result), std::move(impl())));
                    result = std::move(tmp);
                    break;
                }
                default:
                    return result;
            }
        }
    }

    pNode root;
    token cur_token;
    size_t pointer;
    std::string cur_var_name;
    std::string expression;
    std::vector<std::string> vars;
};


int main() {
    std::ios_base::sync_with_stdio(false);
    std::string expression;
    std::cin >> expression;
    ParsingTreeBuilder treeBuilder(expression);
    treeBuilder.parse();


    return 0;
}