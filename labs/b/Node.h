//
// Created by darkey on 3/13/19.
//

#ifndef B_NODE_H
#define B_NODE_H

#include <memory>

class Node;

typedef std::unique_ptr<Node> pNode;

class Node {
public:
    pNode left, right;
    std::string value;

    explicit Node(std::string &&value, pNode left = nullptr, pNode right = nullptr) :
            value(value), hash(0), left(std::move(left)), right(std::move(right)) {}

    explicit Node(std::string &value, pNode left = nullptr, pNode right = nullptr) :
            value(value), hash(0), left(std::move(left)), right(std::move(right)) {}

    void set_hash(unsigned long long hash);

    unsigned long long getLeftChildHash() const;

    unsigned long long getRightChildHash() const;

    bool isLeaf() const;

    unsigned long long getHash() const;

    bool operator==(const Node &other) const {
        return hash == other.hash;
    }

private:
    unsigned long long hash;
};

#endif //B_NODE_H
