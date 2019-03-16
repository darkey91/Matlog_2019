#include <unordered_map>
#include <iostream>
#include <unordered_set>
#include <sstream>
#include <assert.h>
#include "AxiomChecker.h"

constexpr const unsigned long long P_left = 29, P_right = 31;

std::vector<pNode> hyp_ast;

bool is_white(char c) {
    return c == ' ' || c == '\t' || c == '\r';
}

void skip_spaces(const std::string &expression, size_t &pointer) {
    while (pointer < expression.length() && is_white(expression[pointer])) {
        ++pointer;
    }
}


void print(const pNode &node) {
    if (node->isLeaf()) {
        std::cout << node->value;
        return;
    }
    if (node->value != "!") {
        std::cout << "(";
        print(node->left);
        std::cout << " " << node->value << " ";
        print(node->right);
        std::cout << ")";
    } else {
        std::cout << "!";
        print(node->left);
    }
}

enum token {
    BEGIN, OPEN, CLOSE, VAR, OR, AND, IMPL, NOT, END
};

enum came_from : int {
    HYPOTHESIS,
    AXIOM,
    MP,
    WRONG
};

struct expression_wrapper {

    void set_data(enum came_from its, int num_old, int ax_hyp_num) {
        is = its;
        number_in_old_proof = num_old;
        axiom_or_hypothesis_number  = ax_hyp_num;
    }

    bool isProved = false;
    bool isUsed = false;
    enum came_from is = WRONG;
    int number_in_old_proof = -1;
    int axiom_or_hypothesis_number = -1;

    int prefix = -1;
    int suffix = -1;

    unsigned long long hash = 0;

    bool operator==(const expression_wrapper &other) const {
        return hash == other.hash;
    }
};

class ParsingTreeBuilder {
public :
    pNode root = nullptr;

    void parse() {
        root = std::move(impl());
        fillTree(root);
    }

    void setExpression(const std::string &expression) {
        this->expression = expression;
        init();
    }

private :

    void init() {
        cur_token = BEGIN;
        pointer = 0;
    }

    bool partOfName(char c) {
        return ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || c == '\'';
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

    //set spans of tree for each node and counts hash
    void fillTree(const pNode &node) {
        if (node == nullptr || (node->left == nullptr && node->right == nullptr))
            return;

        fillTree(node->left);
        fillTree(node->right);

        if (node->right == nullptr) {
            node->set_hash(node->getLeftChildHash() * P_left + '!');
        } else {
            node->set_hash(node->getLeftChildHash() * P_left + node->getRightChildHash() * P_right + node->value[0]);
            assert(node->value[0] == '-'
                   || node->value[0] == '&'
                   || node->value[0] == '|');
        }
    }

    void get_token() {
        skip_spaces(expression, pointer);
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
                result.reset(new Node(cur_var_name));
                result->set_hash(std::hash<std::string>()(cur_var_name));
                get_token();
                break;
            }
            case NOT : {
                pNode tmp(new Node("!", std::move(ver()), nullptr));
                result = std::move(tmp);
                break;
            }
            case OPEN : {
                result = std::move(impl());
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
                    pNode tmp(new Node("&", std::move(result), std::move(ver())));
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
                    pNode tmp(new Node("|", std::move(result), std::move(conj())));
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
                    pNode tmp(new Node("->", std::move(result), std::move(impl())));
                    result = std::move(tmp);
                    break;
                }
                default:
                    return result;
            }
        }
    }

    token cur_token = BEGIN;
    size_t pointer = 0;
    std::string cur_var_name;
    std::string expression;
};

class Minimizer {
public:
    bool isCorrect = true;

    Minimizer() {
        parseAxioms();
        set_data();
    }

    bool minimize() {
        run();
        if (!correct() || !isCorrect) {
            std::cout << "Proof is incorrect";
            return false;
        } else {
            last_step(wrappers.back());
            return true;
        }
    }

    void print_proof() {
        int cnt = 0;
        for (auto &h: hyp_ast) {
            print(h);
            if (cnt++ < hyp_ast.size() - 1)
                std::cout << ", ";
        }
        std::cout << " |- ";
        print(proposal);
        std::cout << "\n";
        int number = 0;

        std::vector<int> new_number(wrappers.size());
        for (auto &w: wrappers) {
            if (w->isUsed) {
                new_number[w->number_in_old_proof] = number;
                std::cout << "[" << ++number << ".";
                switch (w->is) {
                    case HYPOTHESIS: {
                        std::cout << " Hypothesis " << w->axiom_or_hypothesis_number;
                        break;
                    }
                    case AXIOM: {
                        std::cout << " Ax. sch. " << ++w->axiom_or_hypothesis_number;
                        break;
                    }
                    case MP: {
                        std::cout << " M.P. " << new_number[w->suffix] + 1 << ", " << new_number[w->prefix] + 1;
                        break;
                    }
                    case WRONG: {
                        break;
                    }
                }
                std::cout << "] ";
                print(ast_old_proof[w->number_in_old_proof]);
                std::cout << "\n";
            }
        }
    }

private:
    typedef std::unique_ptr<expression_wrapper> pWrapper;
    ParsingTreeBuilder builder;
    AxiomChecker checker;

    void last_step(const pWrapper &wrapper) {
        assert(wrapper->is != WRONG);

        wrapper->isUsed = true;
        switch (wrapper->is) {
            case HYPOTHESIS: {
                break;
            }
            case AXIOM: {
                break;
            }
            case MP: {
                last_step(wrappers[wrapper->prefix]);
                last_step(wrappers[wrapper->suffix]);
                break;
            }
            default:
                break;
        }
    }

    void parseAxioms() {
        for (size_t i = 0; i < AxiomChecker::N_AXIOM; ++i) {
            builder.setExpression(checker.get_kth_axiom(i));
            builder.parse();
            checker.set_kth_axiom_tree(i, builder.root);
        }
    }

    bool correct() {
        return wrappers.back()->hash == proposal->getHash() && wrappers.back()->isProved;
    }

    void set_data() {
        std::string tmp;
        getline(std::cin, tmp);

        size_t beg = 0;
        size_t hypothesis_number = 0;

        size_t index = 0;
        skip_spaces(tmp, index);

        if (tmp[index] != '|') {
            for (; index < tmp.size(); ++index) {
                if (tmp[index] == ',' || (tmp[index] == '|' && tmp[index + 1] == '-')) {
                    builder.setExpression(tmp.substr(beg, index - beg));
                    builder.parse();
                    hyp_ast.push_back(std::move(builder.root));
                    assert(hyp_ast.back() != nullptr);
                    check_hyp.insert({hyp_ast.back()->getHash(), {hyp_ast.back().get(), ++hypothesis_number}}) ;

                    if (tmp[index] == '|') {
                        index += 2;
                        builder.setExpression(tmp.substr(index));
                        builder.parse();
                        proposal = std::move(builder.root);
                        break;
                    }
                    ++index;
                    skip_spaces(tmp, index);
                    beg = index;
                }
            }
        } else {
            index += 2;
            builder.setExpression(tmp.substr(index));
            builder.parse();
            proposal = std::move(builder.root);
        }

        while (getline(std::cin, tmp)) {
            old_proof.push_back(tmp);
        }
    }

    void run() {
        for (int index = 0; index < old_proof.size(); ++index) {
            builder.setExpression(old_proof[index]);
            builder.parse();

            ast_old_proof.push_back(std::move(builder.root));

            unsigned long long hash = ast_old_proof.back()->getHash();

            pWrapper wrapper = std::make_unique<expression_wrapper>();

            wrapper->number_in_old_proof = index;
            wrapper->hash = hash;

            auto found_hypothesis = check_hyp.find(ast_old_proof.back()->getHash());

            if (found_hypothesis != check_hyp.end()) {
                fill_proved_wrapper(ast_old_proof.back(), wrapper, index, HYPOTHESIS, (int) found_hypothesis->second.second, -1, -1);
            } else {
                int axiom_number = checker.find_axiom(ast_old_proof.back());
                if (axiom_number >= 0) {
                    fill_proved_wrapper(ast_old_proof.back(), wrapper, index, AXIOM, axiom_number, -1, -1);
                } else {
                    //проверяю  mp ли this
                    auto right_subtree = right_set.find(hash);

                    if (right_subtree != right_set.end()) {
                        unsigned long long hash_of_whole_tree = '-' + P_right * hash;
                        expression_wrapper *left = nullptr;
                        for (auto l: right_subtree->second) {
                            auto left_proved_tree = proved.find(l);
                            if (left_proved_tree != proved.end()) {
                                left = left_proved_tree->second;
                            }
                        }
                        if (left != nullptr) {
                            hash_of_whole_tree += (P_left * left->hash);
                            auto pair_wrp = proved.find(hash_of_whole_tree);

                            //If you count hash well 'pair_wrap' should exist
                            assert(pair_wrp != proved.end());
                            expression_wrapper *whole_expr = pair_wrp->second;
                            fill_proved_wrapper(ast_old_proof.back(), wrapper, index, MP, -1,
                                                left->number_in_old_proof, whole_expr->number_in_old_proof);

                        }
                    } else {
                        isCorrect = false;
                    }
                }
            }
            wrappers.emplace_back(std::move(wrapper));
        }
    }

    void fill_proved_wrapper(const pNode &node, const pWrapper &wrapper, int index, enum came_from is, int axiom_number,
                             int prefix, int suffix) {
        wrapper->set_data(is, index, axiom_number);
        if (is == MP) {
            wrapper->prefix = prefix;
            wrapper->suffix = suffix;
        }
        wrapper->isProved = true;
        add_to_right_set(node);
        proved.insert({wrapper->hash, wrapper.get()});
    }

    //это proved_ast, которое имеет в корне '->' и следовательно правое поддерево, левое поддерево
    void add_to_right_set(const pNode &root) {
        if (root->value != "->")
            return;
        auto found_right_ast = right_set.find(root->right->getHash());
        if (found_right_ast != right_set.end()) {
            found_right_ast->second.insert(root->left->getHash());
        } else {
            right_set.insert(std::make_pair(root->right->getHash(),
                                            std::unordered_set<unsigned long long>() = {root->left->getHash()}));
        }
    }

    std::unordered_map<unsigned long long, std::unordered_set<unsigned long long>> right_set;

    std::unordered_map<unsigned long long, expression_wrapper *> proved;

    std::vector<pWrapper> wrappers;

    std::unordered_map<unsigned long long, std::pair<Node *, size_t >> check_hyp;
    pNode proposal;

    std::vector<pNode> ast_old_proof;

    std::vector<std::string> old_proof;
};


int main() {
 Minimizer minimizer;
    if (minimizer.minimize())
        minimizer.print_proof();
    return 0;
}