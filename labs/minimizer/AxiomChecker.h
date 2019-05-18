//
// Created by darkey on 3/13/19.
//

#ifndef B_AXIOMCHECKER_H
#define B_AXIOMCHECKER_H

#include "Node.h"
#include <vector>

class AxiomChecker {
public:
    const static size_t N_AXIOM = 10, MAX_LEAVES = 7;

    /** returns the number of presumed axiom, if structure of node tree is
        * similar to the structure of axiom **/
    int find_axiom(const pNode &node);

    const std::string &get_kth_axiom(size_t k) const;

    void set_kth_axiom_tree(size_t k, pNode &node);

private:
    const std::vector<std::string> axioms = {"(A->(B->A)",
                                             "(A->B)->(A->B->C)->(A->C)",
                                             "A->B->A&B",
                                             "A&B->A", "A&B->B",
                                             "A->A|B",
                                             "B->A|B",
                                             "(A->B)->(C->B)->(A|C->B)",
                                             "(A->B)->(A->!B)->!A",
                                             "A->!A->B" };

    pNode axiomTrees[AxiomChecker::N_AXIOM];

    bool check(const pNode &axiom_root, const pNode &root, int axiom_number, int &childIndex);

    /** if two tree has structure similar to axiom[k]
     * functions returns true if subtrees in necessary places are equal
     * */
    bool is_kth_axiom(int k) const;

    void reset_hashes();

    unsigned long long leaves_hash[N_AXIOM][MAX_LEAVES] = {0};

};


#endif //B_AXIOMCHECKER_H
