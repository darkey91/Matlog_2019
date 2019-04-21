#include "AxiomChecker.h"

bool AxiomChecker::check(const pNode &axiom_node, const pNode &node, int axiom_number, int &index) {
    if (axiom_node->isLeaf()) {
        leaves_hash[axiom_number][index++] = node->getHash();
        return true;
    }

    if ( node == nullptr || axiom_node->value != node->value)
        return false;

    if (axiom_node->value == "!")
        return check(axiom_node->left, node->left, axiom_number, index);

    return check(axiom_node->left, node->left, axiom_number, index) && check(axiom_node->right, node->right, axiom_number, index);
}

bool AxiomChecker::is_kth_axiom(int k) const {
    switch (k) {
        case 0: {
            return leaves_hash[k][0] == leaves_hash[k][2];
        }
        case 1: {

            return leaves_hash[k][0] == leaves_hash[k][2] &&  leaves_hash[k][2] == leaves_hash[k][5] &&
                   leaves_hash[k][1] == leaves_hash[k][3] &&
                   leaves_hash[k][4] == leaves_hash[k][6];
        }
        case 2: {
            return leaves_hash[k][0] == leaves_hash[k][2] &&
                   leaves_hash[k][1] == leaves_hash[k][3];
        }
        case 3 : {
            return leaves_hash[k][0] == leaves_hash[k][2];
        }
        case 4 : {
            return leaves_hash[k][1] == leaves_hash[k][2];
        }
        case 5 : {
            return leaves_hash[k][0] == leaves_hash[k][1];
        }
        case 6 : {
            return leaves_hash[k][0] == leaves_hash[k][2];
        }
        case 7 : {
            return leaves_hash[k][0] == leaves_hash[k][4] &&
                   leaves_hash[k][1] == leaves_hash[k][3] &&  leaves_hash[k][3] == leaves_hash[k][6] &&
                   leaves_hash[k][2] == leaves_hash[k][5];
        }
        case 8 : {
            return leaves_hash[k][0] == leaves_hash[k][2] && leaves_hash[k][2] == leaves_hash[k][4] &&
                   leaves_hash[k][1] == leaves_hash[k][3];
        }
        case 9 : {
            return leaves_hash[k][0] == leaves_hash[k][1];
        }
        case 10: {
            return leaves_hash[k][0] == leaves_hash[k][1];
        }
        default:
            return false;
    }
}

const std::string & AxiomChecker::get_kth_axiom(size_t k) const {
    if (k < N_AXIOM)
        return axioms[k];
    return axioms[0];
}

int AxiomChecker::find_axiom(const pNode &node) {
    for (int i = 0; i < N_AXIOM; ++i) {
        int leafIndex = 0;
        // убери это нахрен, если тлится
        reset_hashes();
        if (check(axiomTrees[i], node, i, leafIndex) && is_kth_axiom(i))
            return i;

    }
    return -1;
}

void AxiomChecker::set_kth_axiom_tree(size_t k, pNode &node) {
    if (k < N_AXIOM)
        axiomTrees[k] = std::move(node);
}

void AxiomChecker::reset_hashes() {
    for (size_t i = 0 ; i < N_AXIOM; ++i) {
        for (size_t j = 0; j < MAX_LEAVES; ++j) {
            leaves_hash[i][j] = 0;
        }
    }
}
