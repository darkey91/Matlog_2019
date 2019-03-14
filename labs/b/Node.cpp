//
// Created by darkey on 3/13/19.
//


#include "Node.h"

void Node::set_hash(unsigned long long hash) {
    this->hash = hash;
}

 unsigned long long Node::getLeftChildHash() const {
    return this->left->hash;
}

 unsigned long long Node::getRightChildHash() const {
    return this->right->hash;
}

 bool Node::isLeaf() const {
    return this->left == nullptr && this->right == nullptr;
}

 unsigned long long Node::getHash() const {
    return this->hash;
}