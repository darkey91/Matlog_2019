#include <unordered_map>
#include <iostream>
#include <unordered_set>
#include <sstream>
#include <climits>
#include <assert.h>
#include "AxiomChecker.h"

constexpr const unsigned long long P = 31;

std::vector<pNode> hyp_ast;

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

    void set_data(enum came_from its, int num_old, int ax_num) {
        is = its;
        number_in_old_proof = num_old;
        axiom_number = ax_num;
    }

    bool isUsed = false;
    enum came_from is = WRONG;
    int number_in_old_proof = -1;
    int axiom_number = -1;

    int prefix = -1;
    int suffix = -1;

    size_t step_amount = 0;
    unsigned long long hash = 0;

    bool operator==(const expression_wrapper &other) const {
        return hash == other.hash;
    }
};

class ParsingTreeBuilder {
public :
    void parse() {
        root = std::move(impl());
        fillTree(root);
    }

    void setExpression(const std::string &expression) {
        this->expression = expression;
        init();
    }

    pNode &getRoot() {
        return root;
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

    void skip_spaces() {
        while (pointer < expression.length() && is_white(expression[pointer])) {
            ++pointer;
        }
    }

    bool is_white(char c) {
    return c == ' ' || c == '\t' || c == '\r';
}

    //set spans of tree for each node and counts hash
    void fillTree(const pNode &node) {
        if (node == nullptr || (node->left == nullptr && node->right == nullptr))
            return;

        fillTree(node->left);
        fillTree(node->right);

        if (node->right == nullptr) {
            node->set_hash(node->getLeftChildHash() * P + '!');
        } else {
            node->set_hash(node->getLeftChildHash() * P * P + node->getRightChildHash() * P + node->value[0]);
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
                result.reset(new Node(cur_var_name));
                result->set_hash(get_hash_for_string(cur_var_name));
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

    pNode root = nullptr;
    token cur_token = BEGIN;
    size_t pointer = 0;
    std::string cur_var_name;
    std::string expression;

    //calculates hash for string
    unsigned long long get_hash_for_string(const std::string &str) {
        unsigned long long res = str[0];

        for (size_t i = 1; i < str.size(); ++i) {
            res = res * P + str[0];
        }

        return res;
    }
};

class Minimizer {
public:
    Minimizer() {
        parseAxioms();
        set_data();
        last_proof_string = old_proof.size() - 1;
    }

    bool minimize() {
        run();
        expression_wrapper *wr = wrappers[last_proof_string].get();
        if (!correct()) {
            std::cout << "Proof is incorrect";
            return false;
        } else {
            last_step(wrappers[last_proof_string]);
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
        int hyp = 0;
        std::vector<int> new_number(wrappers.size());
        for (auto &w: wrappers) {
            if (w->isUsed) {
                new_number[w->number_in_old_proof] = number;
                std::cout << "[" << ++number << ".";
                switch (w->is) {
                    case HYPOTHESIS: {
                        std::cout << " Hypothesis " << ++hyp;
                        break;
                    }
                    case AXIOM: {
                        std::cout << " Ax. sch. " << ++w->axiom_number;
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

    void print_old() {
        int number = 0;
        for (auto &w: wrappers) {
            std::cout << "[" << ++number << ".";
            switch (w->is) {
                case HYPOTHESIS: {
                    std::cout << " Hypothesis ";
                    break;
                }
                case AXIOM: {
                    std::cout << " Ax. sch. " << ++w->axiom_number;
                    break;
                }
                case MP: {
                    std::cout << " M.P. " << w->suffix + 1 << ", " << w->prefix + 1;
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

private:
    typedef std::unique_ptr<expression_wrapper> pWrapper;
    ParsingTreeBuilder builder;
    AxiomChecker checker;

    void last_step(const pWrapper &wrapper) {
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
            case WRONG: {
                //по идее, сюда не должен заходить
                wrapper->isUsed = false;
                break;
            }
        }
    }


    void parseAxioms() {
        for (size_t i = 0; i < AxiomChecker::N_AXIOM; ++i) {
            builder.setExpression(checker.get_kth_axiom(i));
            builder.parse();
            checker.set_kth_axiom_tree(i, builder.getRoot());
        }
    }

    bool correct() {
        return !wrappers.empty() && proved.count(wrappers[last_proof_string]->hash) > 0;
    }

    void set_data() {
        std::string tmp;
        getline(std::cin, tmp);

        size_t beg = 0;
        if (tmp[0] != '|') {
            for (size_t i = 0; i < tmp.size(); ++i) {
                if (tmp[i] == ' ') {
                    continue;
                }
                if (tmp[i] == ',' || (tmp[i] == '|' && tmp[i + 1] == '-')) {
                    builder.setExpression(tmp.substr(beg, i - beg));
                    builder.parse();

                    hyp_ast.push_back(std::move(builder.getRoot()));
                    assert(hyp_ast.back() != nullptr);
                    check_hyp.insert(hyp_ast.back()->getHash());

                    if (tmp[i] == '|') {
                        ++i;
                        while (tmp[i] == ' ' || tmp[i] == '-')
                            ++i;

                        builder.setExpression(tmp.substr(i, tmp.size() - i));
                        builder.parse();
                        proposal = std::move(builder.getRoot());
                        break;
                    }
                    while (tmp[i + 1] == ' ')
                        ++i;
                    beg = i + 1;
                }
            }
        } else {
            builder.setExpression(tmp.substr(2));
            builder.parse();
            proposal = std::move(builder.getRoot());
        }
        int i = 0;
        while (getline(std::cin, tmp)) {
            old_proof.push_back(tmp);
            ++i;
        }
    }

    void run() {
        for (int index = 0; index < old_proof.size(); ++index) {
            builder.setExpression(old_proof[index]);
            builder.parse();

            ast_old_proof.push_back(std::move(builder.getRoot()));

            unsigned long long hash = ast_old_proof.back()->getHash();

            pWrapper wrapper = std::make_unique<expression_wrapper>();

            wrapper->number_in_old_proof = index;
            wrapper->hash = hash;

            bool isHypothesis = check_hyp.find(ast_old_proof.back()->getHash()) != check_hyp.end();

            if (isHypothesis) {
                fill_proved_wrapper(ast_old_proof.back(), wrapper, index, HYPOTHESIS, -1, 1, -1, -1);
            } else {
                int axiom_number = checker.find_axiom(ast_old_proof.back());
                if (axiom_number >= 0) {
                    fill_proved_wrapper(ast_old_proof.back(), wrapper, index, AXIOM, axiom_number, 1, -1, -1);
                } else {
                    //проверяю  mp ли this
                    auto right_subtree = right_set.find(hash);

                    if (right_subtree != right_set.end()) {
                        unsigned long long hash_of_whole_tree = '-' + P * hash;
                        expression_wrapper *left = nullptr;
                        size_t MIN_BY_STEP = INT_MAX;
                        for (auto l: right_subtree->second) {
                            auto left_proved_tree = proved.find(l);
                            if (left_proved_tree != proved.end()) {
                                left = left_proved_tree->second;
                                if (MIN_BY_STEP > left_proved_tree->second->step_amount) {
                                    left = left_proved_tree->second;
                                    MIN_BY_STEP = left->step_amount;
                                }
                            }
                        }

                        if (left != nullptr) {
                            hash_of_whole_tree += (P * P * left->hash);
                            auto pair_wrp = proved.find(hash_of_whole_tree);
                            if (pair_wrp != proved.end()) {
                                expression_wrapper *whole_expr = pair_wrp->second;
                                fill_proved_wrapper(ast_old_proof.back(), wrapper, index, MP, -1,
                                                    left->step_amount + whole_expr->step_amount + 1,
                                                    left->number_in_old_proof, whole_expr->number_in_old_proof);
                            } else {
                                std::cout << "congruts! you have done a piece of sh.t\n";
                            }
                        }
                    }
                }
            }
            wrappers.emplace_back(std::move(wrapper));
        }
    }

    void fill_proved_wrapper(const pNode &node, const pWrapper &wrapper, int index, enum came_from is, int axiom_number,
                             size_t step_addition, int prefix, int suffix) {
        wrapper->set_data(is, index, axiom_number);
        wrapper->step_amount += step_addition;
        if (is == MP) {
            wrapper->prefix = prefix;
            wrapper->suffix = suffix;
        }

        add_to_right_set(node);
        proved.insert({wrapper->hash, wrapper.get()});

        if (node->getHash() == proposal->getHash()) {
            wrapper->isUsed = true;
            if (last_proof_string > index) {
                last_proof_string = index;
            }
        }
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

    std::unordered_set<unsigned long long> check_hyp;
    pNode proposal;
    int last_proof_string;

    std::vector<pNode> ast_old_proof;

    std::vector<std::string> old_proof;
};


int main() {
    Minimizer minimizer;
    if (minimizer.minimize())
        minimizer.print_proof();
    return 0;
}