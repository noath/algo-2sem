#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <ctime>
#include <tuple>
#include <functional>

typedef long long ll;

class ImplicitTreap {
private:
    struct Node {
        ll pr_;
        ll val_;
        ll left_;
        ll right_;
        ll add_;
        ll sumTree_;
        bool isDirectTree_;
        bool isReversedTree_;
        bool rev_;
        bool assign_to_zero_;
        ll size_;
        Node *l;
        Node *r;

        static std::mt19937 gen;
        static std::uniform_int_distribution<ll> uniform_distribution;
        static ll randint() {
            return uniform_distribution(gen);
        }

        Node() : pr_(randint()), val_(0), left_(0), right_(0),
                 isDirectTree_(true), isReversedTree_(true), rev_(false), assign_to_zero_(false),
                 sumTree_(0), add_(0), size_(1), l(nullptr), r(nullptr) {}

        explicit Node(ll val) : pr_(randint()), val_(val), left_(val), right_(val),
                                isDirectTree_(true), isReversedTree_(true), rev_(false), assign_to_zero_(false),
                                sumTree_(val_), add_(0), size_(1), l(nullptr), r(nullptr) {}

        ~Node(){
            delete l;
            delete r;
        }

        ll size() const {
            return this == nullptr ? 0 : size_;
        }

        ll sumTree() const {
            return this == nullptr ? 0 : sumTree_;
        }

        void add_recalc(ll delta) {
            if (this == nullptr)
                return;
            val_ += delta;
            sumTree_ += size() * delta;
            left_ += delta;
            right_ += delta;
        }

        void update_assign_to_zero() {
            if (this == nullptr)
                return;
            isDirectTree_ = true;
            isReversedTree_ = true;
            val_ = 0;
            left_ = 0;
            right_ = 0;
            sumTree_ = 0;
            add_ = 0;
        }

        void push_reverse() {
            if (this == nullptr)
                return;
            if (rev_) {
                rev_ = false;
                std::swap(left_, right_);
                std::swap(l, r);
                std::swap(isDirectTree_, isReversedTree_);
                if (l != nullptr)
                    l->rev_ ^= true;
                if (r != nullptr)
                    r->rev_ ^= true;
            }
        }

        void push_zero() {
            if (assign_to_zero_) {
                l->update_assign_to_zero();
                r->update_assign_to_zero();
                if (l != nullptr)
                    l->assign_to_zero_ = true;
                if (r != nullptr)
                    r->assign_to_zero_ = true;
                assign_to_zero_ = false;
            }
        }

        void push_add() {
            if (add_ != 0) {
                l->add_recalc(add_);
                r->add_recalc(add_);
                if (l != nullptr)
                    l->add_ += add_;
                if (r != nullptr)
                    r->add_ += add_;
                add_ = 0;
            }
        }

        void push() {
            if (this == nullptr)
                return;
            push_reverse();
            push_zero();
            push_add();
        }

        template<bool isDirect = false>
        void update_reverse() {
            if (this == nullptr)
                return;

            bool isOrderedTree = isDirect ? isDirectTree_ : isReversedTree_;
            if (l == nullptr && r == nullptr)
                isOrderedTree = true;
            else if (l != nullptr && r == nullptr) {
                isOrderedTree = isDirect ? (l->isDirectTree_ && l->right_ <= val_) :
                                (l->isReversedTree_ && l->right_ >= val_);
            } else if (l == nullptr && r != nullptr) {
                isOrderedTree = isDirect ? (r->isDirectTree_ && r->left_ >= val_) :
                                (r->isReversedTree_ && r->left_ <= val_);
            } else if (l != nullptr && r != nullptr) {
                isOrderedTree = isDirect ? (l->isDirectTree_ && r->isDirectTree_
                                            && l->right_ <= val_ && r->left_ >= val_) :
                                (l->isReversedTree_ && r->isReversedTree_
                                 && l->right_ >= val_ && r->left_ <= val_);
            }

            (isDirect ? isDirectTree_ : isReversedTree_) = isOrderedTree;
        }

        void update() {
            if (this == nullptr)
                return;

            l->push();
            r->push();

            size_ = l->size() + r->size() + 1;
            sumTree_ = l->sumTree() + r->sumTree() + val_;

            update_reverse<true>();  //updating isDirectTree_
            update_reverse<false>(); //updating isReverseTree_
            //updating left_ and right_
            left_ = l ? l->left_ : val_;
            right_ = r ? r->right_ : val_;
        }

        void assign(ll assignment) {
            assign_to_zero_ = true;
            update_assign_to_zero();
            add_ = assignment;
            add_recalc(assignment);
        }
    };

    explicit ImplicitTreap(Node *t) : root_(t) {}

    typedef std::pair<Node *, Node *> nodes;

    Node *root_;

    template<bool isDirect = false>
    static nodes split(Node *t, ll key, ll add = 0) {
        if (t == nullptr) {
            return nodes(nullptr, nullptr);
        }
        t->push();
        nodes ret_tree;

        ll cmp_val;
        cmp_val = isDirect ? t->val_ - 1 : add + t->l->size();

        if (key > cmp_val) {
            nodes tmp = split<isDirect>(t->r, key, add + 1 + t->l->size());
            t->r = tmp.first;
            ret_tree.first = t;
            ret_tree.second = tmp.second;
        } else {
            nodes tmp = split<isDirect>(t->l, key, add);
            t->l = tmp.second;
            ret_tree.first = tmp.first;
            ret_tree.second = t;
        }

        t->update();
        return ret_tree;
    }

    static Node *merge(Node *l, Node *r) {
        l->push();
        r->push();
        if (l == nullptr)
            return r;
        if (r == nullptr)
            return l;
        if (l->pr_ <= r->pr_) {
            r->l = merge(l, r->l);
            r->update();
            return r;
        } else {
            l->r = merge(l->r, r);
            l->update();
            return l;
        }
    }

    std::tuple<Node*, Node*, Node*> prepare(ll l, ll r) {
        Node *left, *mid, *right;
        nodes tmp1 = split(root_, r + 1);
        mid = tmp1.first;
        right = tmp1.second;

        nodes tmp2 = split(mid, l);
        left = tmp2.first;
        mid = tmp2.second;
        return std::make_tuple(left, mid, right);
    }

    template<typename U>
    ll operate(U lambda, ll l, ll r) {
        Node *left, *mid, *right;
        std::tie(left,mid,right) = prepare(l, r);
        ll ret_value = lambda(mid);
        root_ = merge(merge(left, mid), right);
        return ret_value;
    }

    template<bool isDirect>
    static ll len_of_suffix(Node *t) {
        if (t == nullptr)
            return 0;
        t->push();
        t->l->push();
        t->r->push();

        if (t->l) {
            t->l->l->push();
            t->l->r->push();
        }
        if (t->r) {
            t->r->l->push();
            t->r->r->push();
        }
        if (isDirect)
            return (t->r && !t->r->isDirectTree_) ? 1 + t->l->size() + len_of_suffix<isDirect>(t->r) :
                   (t->r && t->val_ > t->r->left_) ? 1 + t->l->size() :
                   (t->l && t->val_ < t->l->right_) ? t->l->size() : len_of_suffix<isDirect>(t->l);
        else
            return (t->r && !t->r->isReversedTree_) ? 1 + t->l->size() + len_of_suffix<isDirect>(t->r) :
                   (t->r && t->val_ < t->r->left_) ? 1 + t->l->size() :
                   ((t->l && t->val_ > t->l->right_) ? t->l->size() : len_of_suffix<isDirect>(t->l));

    }

    template<bool isNext>
    ll apply_permutation(Node *&t) {
        bool isOrderedTree = isNext ? t->isReversedTree_ : t->isDirectTree_;

        if (isOrderedTree) {
            t->rev_ = true;
            return -1;
        }

        ll len = isNext ? len_of_suffix<false>(t) : len_of_suffix<true>(t);
        Node *left_s, *broken, *right_s;

        nodes tmp1 = split(t, len - 1);
        left_s = tmp1.first;
        right_s = tmp1.second;

        nodes tmp2 = split(right_s, 1);
        broken = tmp2.first;
        right_s = tmp2.second;

        right_s->rev_ |= isNext;

        Node *suf_left, *suf_right, *near_node; //next or prev

        nodes dir_tmp = split<true>(right_s, broken->val_ - (1 - int(isNext)));
        suf_left = dir_tmp.first;
        suf_right = dir_tmp.second;

        nodes tmp5 = isNext ? split(suf_right, 1) : split(suf_left, suf_left->size() - 1);
        near_node = isNext ? tmp5.first : tmp5.second;

        if (isNext) {
            suf_right = tmp5.second;
            t = merge(merge(merge(merge(left_s, near_node), suf_left), broken), suf_right);
        } else {
            suf_left = tmp5.first;
            if (suf_right != nullptr)
                suf_right->rev_ = true;
            if (suf_left != nullptr)
                suf_left->rev_ = true;

            t =  merge(merge(merge(merge(left_s, near_node), suf_right), broken), suf_left);
        }
        return -1;
    }

    void in_order(Node *t, std::vector<ll> &array) {
        if (t == nullptr)
            return;
        t->push();
        in_order(t->l, array);
        array.push_back(t->val_);
        in_order(t->r, array);
    }

public:
    ImplicitTreap() : root_(nullptr) {};

    ~ImplicitTreap() {
        delete root_;
    }

    ll sum_on(ll l, ll r) {
        return operate([](Node *&x) {
            return x->sumTree();
        }, l, r);
    }

    void assign_on(ll assignment, ll l, ll r) {
        operate([assignment](Node *&x) {
            x->assign(assignment);
            return -1;
        }, l, r);
    }

    void increase_on(ll delta, ll l, ll r) {
        operate([delta](Node *&x) {
            x->add_ += delta;
            x->add_recalc(delta);
            return -1;
        }, l, r);
    }

    void remove(ll pos) {
        operate([](Node *&x) {
            delete x;
            x = nullptr;
            return -1;
        }, pos, pos);
    }

    void insert(ll pos, ll x) {
        Node *left, *right;

        nodes tmp(split(root_, pos));
        left = tmp.first;
        right = tmp.second;

        root_ = merge(merge(left, new Node(x)), right);
    }

    void next_permutation(ll l, ll r) {
        operate([this](Node *&x){
            ImplicitTreap::apply_permutation<true>(x);
            return -1;
        }, l, r);
    }

    void prev_permutation(ll l, ll r) {
        operate([this](Node *&x){
            ImplicitTreap::apply_permutation<false>(x);
            return -1;
        }, l, r);
    }

    std::vector<ll> extract() {
        std::vector <ll> array;
        in_order(root_, array);
        return array;
    }
};
std::mt19937 ImplicitTreap::Node::gen = std::mt19937(unsigned(time(nullptr)));
std::uniform_int_distribution<ll> ImplicitTreap::Node::uniform_distribution = std::uniform_int_distribution<ll>(-UINT32_MAX, UINT32_MAX);

enum query_types {sum = 1, ins = 2, rmv = 3, assign = 4, increase = 5, next_perm = 6, prev_perm = 7};
class IQuery {
public:
    IQuery() = default;
    ~IQuery() = default;
    virtual void handle(ImplicitTreap *tree) = 0;
    query_types getType() {
        return type_;
    }
protected:
    query_types type_;
};

class SumQuery : public IQuery{
private:
    ll l_, r_;
public:
    SumQuery() : l_(0), r_(0) {
        type_ = sum;
    };
    explicit SumQuery(ll l, ll r) : l_(l), r_(r){
        type_ = sum;
    };
    void handle(ImplicitTreap *t) override {
        sums_.push_back(t->sum_on(l_, r_));
    }
    static std::vector<ll> sums_;
};
std::vector<ll> SumQuery::sums_ = {};

void print_sums(std::ostream &out_stream = std::cout){
    for (auto &sum : SumQuery::sums_){
        out_stream << sum << "\n";
    }
}

class InsertQuery : public IQuery{
private:
    ll pos_, value_;
public:
    InsertQuery() : pos_(0), value_(0){
        type_ = ins;
    };
    explicit InsertQuery(ll pos, ll value) : pos_(pos), value_(value) {
        type_ = ins;
    };
    void handle(ImplicitTreap *t) override {
        t->insert(pos_, value_);
    }
};

class RemoveQuery : public IQuery{
private:
    ll pos_;
public:
    RemoveQuery() : pos_(0) {
        type_ = rmv;
    };
    explicit RemoveQuery(ll pos) : pos_(pos) {
        type_ = rmv;
    };
    void handle(ImplicitTreap *t) override {
        t->remove(pos_);
    }
};

class AssignmentQuery : public IQuery{
private:
    ll l_, r_, value_;
public:
    AssignmentQuery() : l_(0), r_(0), value_(0) {
        type_ = assign;
    };
    explicit AssignmentQuery(ll value, ll l, ll r) :  value_(value), l_(l), r_(r) {
        type_ = assign;
    };
    void handle(ImplicitTreap *t) override {
        t->assign_on(value_, l_, r_);
    }
};

class IncreaseQuery : public IQuery{
private:
    ll l_, r_, delta_ {};
public:
    IncreaseQuery() : l_(0), r_(0), delta_(0) {
        type_= increase;
    };
    explicit IncreaseQuery(ll value, ll l, ll r) : delta_(value), l_(l), r_(r) {
        type_= increase;
    };
    void handle(ImplicitTreap *t) override {
        t->increase_on(delta_, l_, r_);
    }
};

class PermutationQuery : public IQuery{
private:
    ll l_, r_;
    bool isNext_;
public:
    PermutationQuery() : l_(0), r_(0), isNext_(true){
        type_ = next_perm;
    };
    explicit PermutationQuery(ll l, ll r, bool isNext) : l_(l), r_(r), isNext_(isNext) {
        type_ = (isNext ? next_perm : prev_perm);
    };
    void handle(ImplicitTreap *t) override {
        if (isNext_)
            t->next_permutation(l_, r_);
        else
            t->prev_permutation(l_, r_);
    }
};

std::vector<ll> read_data(std::istream &in_stream = std::cin){
    std::vector<ll> array;
    ll n;
    in_stream >> n;
    for (int i = 0; i < n; i++) {
        ll value;
        in_stream >> value;
        array.push_back(value);
    }
    return array;
}

ImplicitTreap* construct_tree(std::vector<ll> &array){
    auto tree = new ImplicitTreap();
    for (int i = 0; i < array.size(); i++){
        tree->insert(i, array[i]);
    }
    array.clear();
    return tree;
}

void print_treap(std::vector<ll> extracted_tree, std::ostream &out_stream = std::cout){ ;
    for (auto &i: extracted_tree) {
        out_stream << i << " ";
    }
    out_stream << std::endl;
}

std::vector<IQuery*> read_queries(std::istream &in_stream = std::cin){
    auto QueryManager = new std::vector<IQuery*>();
    ll q, l, r, pos, x;
    short mode;
    in_stream >> q;
    for (ll i = 0; i < q; i++) {
        in_stream >> mode;
        if (mode == sum) {
            in_stream >> l >> r;
            QueryManager->push_back(dynamic_cast<IQuery*>(new SumQuery(l, r)));
        } else if (mode == ins) {
            in_stream >> x >> pos;
            QueryManager->push_back(dynamic_cast<IQuery*>(new InsertQuery(pos, x)));
        } else if (mode == rmv) {
            in_stream >> pos;
            QueryManager->push_back(dynamic_cast<IQuery*>(new RemoveQuery(pos)));
        } else if (mode == assign) {
            in_stream >> x >> l >> r;
            QueryManager->push_back(dynamic_cast<IQuery*>(new AssignmentQuery(x, l, r)));
        } else if (mode == increase) {
            in_stream >> x >> l >> r;
            QueryManager->push_back(dynamic_cast<IQuery*>(new IncreaseQuery(x, l, r)));
        } else if (mode == next_perm) {
            in_stream >> l >> r;
            QueryManager->push_back(dynamic_cast<IQuery*>(new PermutationQuery(l, r, true)));
        } else if (mode == prev_perm) {
            in_stream >> l >> r;
            QueryManager->push_back(dynamic_cast<IQuery*>(new PermutationQuery(l, r, false)));
        }
    }
    return *QueryManager;
}

void operate_queries(std::vector <IQuery *> QueryManager, ImplicitTreap *tree){
    for (auto &query : QueryManager){
        query->handle(tree);
    }
}

std::pair<std::vector<ll>, std::vector<IQuery*>> input(std::istream &in_stream = std::cin){
    auto data = read_data(in_stream);
    auto query = read_queries(in_stream);
    return {data, query};
}

class InputData{
private:
    std::vector<ll> elems;
    std::vector<IQuery*> query;
public:
    std::vector<ll> getElems(){
        return elems;
    }
    std::vector<IQuery*> getQuery(){
        return query;
    }
    explicit InputData(std::vector<ll> a, std::vector<IQuery*> b) : elems(std::move(a)), query(std::move(b)) {};
    explicit InputData(std::pair<std::vector<ll>, std::vector<IQuery*>> p) :
            elems(p.first), query(p.second) {};

    InputData(const InputData &other) : elems(other.elems){
        query.clear();
        for (int i = 0; i < other.query.size(); i++){
            switch (other.query[i]->getType()) {
                case sum:{
                    SumQuery *new_node = dynamic_cast<SumQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
                case rmv: {
                    RemoveQuery *new_node = dynamic_cast<RemoveQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
                case ins: {
                    InsertQuery *new_node = dynamic_cast<InsertQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
                case assign: {
                    AssignmentQuery *new_node = dynamic_cast<AssignmentQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
                case increase: {
                    IncreaseQuery *new_node = dynamic_cast<IncreaseQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
                default: {
                    PermutationQuery *new_node = dynamic_cast<PermutationQuery*>(other.query[i]);
                    query.push_back(new_node);
                    break;
                }
            }
        }
    }
    InputData& operator=(const InputData &other){
        *this = InputData(other);
        return *this;
    }
};

class OutputData{
private:
    std::vector<ll> sums;
    std::vector<ll> extracted_tree;
public:
    std::vector<ll> getSums(){
        return sums;
    }
    std::vector<ll> getExtractedTree(){
        return extracted_tree;
    }

    explicit OutputData(std::vector<ll> a, std::vector<ll> b) : sums(std::move(a)), extracted_tree(std::move(b)) {};
    explicit OutputData(std::pair<std::vector<ll>, std::vector<ll>> p) :
            sums(p.first), extracted_tree(p.second) {};

    OutputData(const OutputData &other) : sums(other.sums), extracted_tree(other.extracted_tree) {}
    OutputData& operator=(const OutputData &other){
        *this = OutputData(other);
        return *this;
    }
};

OutputData process_tree(InputData inp_data){
    auto data_for_tree = inp_data.getElems();
    auto tree = construct_tree(data_for_tree);
    auto query_manager = inp_data.getQuery();
    operate_queries(query_manager, tree);
    auto extracted_tree = tree->extract();

    return OutputData(SumQuery::sums_, extracted_tree);
}

void output(OutputData out, std::ostream &out_stream = std::cout){
    print_sums(out_stream);
    print_treap(std::move(out.getExtractedTree()), out_stream);
}

void solve(std::istream &in_stream = std::cin, std::ostream &out_stream = std::cout) {
    auto input_data = InputData(input());

    OutputData output_data = process_tree(input_data);

    output(output_data);
}

int main() {
    solve();
    return 0;
}

