#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <set>
#include <functional>
#include <map>


//Order of Operations: 
// 1. Quantifiers/Negations (!, ?, ~)
// 2. Conjunction (&)
// 3. Disjunction (|)
// 4. Implication/Equivalence ( =>, <=>)


//
//----------------------------------PARSER-------------------------------------

//AST Node

enum class NodeType {
    ATOM, NOT, AND, OR, IMPLY, EQUIV, FORALL, EXISTS
};

struct Node {
    NodeType type;
    std::string name; //for predicate names or variables
    std::vector<std::shared_ptr<Node>> children;
    std::set<std::string> usedTerms;

    //Helper for Atoms: p(X, Y)
    Node(NodeType t, std::string n) : type(t), name(n) {}
    
    //Helper for unary/binary
    Node(NodeType t, std::shared_ptr<Node> left, std::shared_ptr<Node> right = nullptr)
        : type(t) {
        children.push_back(left);
        if (right) children.push_back(right);
        }
    
    //Quantifier Constructor
    Node(NodeType t, std::string n, std::shared_ptr<Node> body) 
        : type(t), name(n) {
        children.push_back(body);
    }
    
    std::string toString() const {
        if(type == NodeType::ATOM){
            if (children.empty()) return name;
            std::string s = name + "(";
            for(size_t i = 0; i < children.size(); ++i) {
                s += children[i] -> toString();
                if(i < children.size() - 1) s += ", ";
            }
            return s + ")";
        }
        if (type == NodeType::NOT) return "~" + children[0]->toString();

        std::string op = "";
        if (type == NodeType::AND) op = " & ";
        else if (type == NodeType:: OR) op = " | ";
        else if (type == NodeType:: IMPLY) op = " =>";
        else if (type == NodeType:: EQUIV) op = " <=> ";

        if (op != ""){
            return "(" + children[0]->toString() + op + children[1]->toString() + ")";
        }

        if (type == NodeType::FORALL) return "![ " + name + " ] : " + children[0]->toString();
        if (type == NodeType::EXISTS) return "?[ " + name + " ] : " + children[0]->toString();

        return "???";
    }

};

//Lexer (Tokeniser)

struct Token {
    enum Type{
        FOF, LPAREN, RPAREN, LBRACKET, RBRACKET, COMMA, PERIOD, COLON,
        NOT, AND, OR, IMPLY, EQUIV, FORALL, EXISTS, ID, VAR, END}; 
        Type type;
        std::string value;
};

class Lexer {
    std::string input;
    size_t pos = 0;
public: 
    Lexer(std::string s) : input(s) {}
    Token nextToken() {
        //skip whitespace
        while(pos < input.length() && isspace(input[pos])) pos++;
        if(pos >= input.length()) return { Token::END, ""};
        
        //check multi-char symbols
        if(pos + 2 < input.length() && input.substr(pos, 3) == "<=>"){
            pos += 3;
            return { Token::EQUIV, "<=>"};
        }
        if(pos + 1 < input.length() && input.substr(pos, 2) == "=>"){
            pos += 2;
            return {Token::IMPLY, "=>" };
        }

        //check single-char symbols 
        char c = input[pos];
        switch (c) {
            case '(': pos++; return { Token::LPAREN, "("};
            case ')': pos++; return { Token::RPAREN, ")"};
            case '!': pos++; return { Token::FORALL, "!"};
            case '?': pos++; return { Token::EXISTS, "?"};
            case '&': pos++; return { Token::AND, "&"};
            case '|': pos++; return { Token::OR, "|"};
            case '~': pos++; return { Token::NOT, "~"};
            case ':': pos++; return { Token::COLON, ":"};
            case '[': pos++; return { Token::LBRACKET, "["};
            case ']': pos++; return { Token::RBRACKET, "]"};
            case ',': pos++; return { Token::COMMA, ","};
            case '.': pos++; return { Token::PERIOD, "."};
        }
        //check identifiers
        if(isalnum(c) || c == '_') {
            std::string value = "";
            while (pos < input.length() && (isalnum(input[pos]) || input[pos] == '_')) {
                value += input[pos++];
            }
            //Rule: start with uppercase = variable
            if (isupper(value[0])) return {Token::VAR, value};
            //Rule: "fof" is keyword
            if (value == "fof") return {Token::FOF, value};
            //otherwise it's a predicate/constant ID
            return {Token::ID, value};
        }
            pos++; 
            return { Token::END, "ERROR" };
        }
    }; 

// Parser

class Parser {
    std::vector<Token> tokens;
    size_t current = 0;

    Token peek() {return tokens[current]; }
    Token advance() {return tokens[current++]; }

    Token match(Token::Type type) {
        if (peek().type == type) return advance();
        throw std::runtime_error("Unexpected Token");
    }
public:
    Parser(std::vector<Token> t) : tokens(t) {}
    //precedence
    std::shared_ptr<Node> parseFormula() {return parseImplication();}
    std::shared_ptr<Node> parseImplication() {
        auto left = parseDisjunction(); //step down to higher priority
        while (peek().type == Token::IMPLY || peek().type == Token::EQUIV) {
            Token op = advance();
            auto right = parseDisjunction();
            left = std::make_shared<Node>((op.type == Token::IMPLY ? NodeType::IMPLY : NodeType::EQUIV), left, right);
        }
        return left;
        };
    std::shared_ptr<Node> parseDisjunction() {
        auto left = parseConjunction();
        while (peek().type == Token::OR) {
            advance();
            auto right = parseConjunction();
            left = std::make_shared<Node>(NodeType::OR, left, right);
        }
        return left;
        };
    std::shared_ptr<Node> parseConjunction() {
        auto left = parseUnary();
        while (peek().type == Token::AND) {
            advance();
            auto right = parseUnary();
            left = std::make_shared<Node>(NodeType::AND, left, right);
        }
        return left;
        };
    //parsing TPTP Wrapper
    //entry point: fof(name, role, formula)
    std::shared_ptr<Node> buidNestedQuantifier(NodeType type, std::vector<std::string>& vars, std::shared_ptr<Node> body) {
        for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
            body = std::make_shared<Node>(type, *it, body);
        }
        return body;
    }
    std::shared_ptr<Node> parseTopLevel() {
        match(Token::FOF); match(Token::LPAREN);
        std::string name = match(Token::ID).value; match(Token::COMMA);
        std::string role = match(Token::ID).value; match(Token::COMMA);

        auto formula = parseFormula();

        match(Token::RPAREN); match(Token::PERIOD);
        return formula;
    } 
    //Parsing Quantifiers
    std::shared_ptr<Node> parseQuantifier() {
        auto type = (peek().type == Token::FORALL) ? NodeType::FORALL : NodeType::EXISTS;
        advance(); //consume ! or ? 
        match(Token::LBRACKET);

        std::vector<std::string> vars;
        while(peek().type != Token::RBRACKET){
            vars.push_back(match(Token::VAR).value);
            if(peek().type == Token::COMMA) advance();
        }
        match(Token::RBRACKET);
        match(Token::COLON);

        return buidNestedQuantifier(type, vars, parseFormula());
    };
    std::shared_ptr<Node> parseUnary() {
        if (peek().type == Token::NOT) {
            advance();
            return std::make_shared<Node>(NodeType::NOT, parseUnary());
        }
        if (peek().type == Token:: FORALL || peek().type == Token::EXISTS) {
            return parseQuantifier();
        }
        if (peek().type == Token::LPAREN) {
            advance();
            auto node = parseImplication();
            match(Token::RPAREN);
            return node;
        }
        return parseAtom();
        };
    std::shared_ptr<Node> parseAtom() {
        Token t = match(Token::ID);
        auto node = std::make_shared<Node>(NodeType::ATOM, t.value);

        if (peek().type == Token::LPAREN) {
            advance();
            while (peek().type != Token::RPAREN) {
                if(peek().type == Token::VAR) {
                    node->children.push_back(std::make_shared<Node>(NodeType::ATOM, advance().value));
                } else if (peek().type == Token::ID) {
                    node->children.push_back(parseAtom());
                }
                if(peek().type == Token::COMMA) advance();
            }
            match(Token::RPAREN);
        }
        return node;
        };
};

//--------------------------------ALGORITHM------------------------------------

//Sequent Structure

struct Sequent { 
    std::vector<std::shared_ptr<Node>> antecedent; //LHS
    std::vector<std::shared_ptr<Node>> succedent; //RHS

    bool nodesAreEqual(std::shared_ptr<Node> n1, std::shared_ptr<Node> n2) const{
        if(!n1 || !n2) return n1 == n2;
        if(n1->type != n2->type || n1->name != n2->name) return false;
        if(n1->children.size() != n2->children.size()) return false;
        for(size_t i = 0; i < n1->children.size(); i++){
            if(!nodesAreEqual(n1->children[i], n2->children[i])) return false;
        }
        return true;
    }

    //check if atom exists on both sides (ID/closure)
    bool isClosed() const {
        for (const auto& a: antecedent) {
            if(a->type != NodeType::ATOM) continue;
            for (const auto& s : succedent) {
                if(s->type == NodeType::ATOM && nodesAreEqual(a, s)) return true;
                }
            }
        return false;
    }

    std::set<std::string> getExistingTerms() const{
        std::set<std::string> terms;
        std::function<void(std::shared_ptr<Node>)> find = [&](std::shared_ptr<Node> n){
            if (n->type == NodeType::ATOM && n->children.empty()) {
                terms.insert(n->name);
            }
            for (auto& child : n->children) find(child);
        };
        for (auto& f : antecedent) find(f);
        for (auto& f : succedent) find(f);
        return terms;
    }


    void print(int depth) const {
        for(int i = 0; i < depth; i++){ 
            std::cout << "| ";}
    
        std::string lhs = "";

        //print antecedent
        for (size_t i = 0; i < antecedent.size(); ++i){
            lhs += antecedent[i]->toString() + (i == antecedent.size() - 1 ? "" : ", ");
        }
        
        std::string rhs = "";
        //print succedent
        for (size_t i = 0; i < succedent.size(); i++){
            rhs += succedent[i]->toString() + (i == succedent.size() - 1 ? "" : ", ");
        }
        std::cout << (lhs.empty()? "" : lhs + " ") << " |- " << rhs << std::endl; //turnstile
    }
};

//Prover

class Prover {
    int varCounter = 0;
    std::string getFreshTerm() {
        return "t" + std::to_string(varCounter++);
    }
public:
    using UsedRegistry = std::map<std::shared_ptr<Node>, std::set<std::string>>;
    bool prove(Sequent s, UsedRegistry used, int depth = 0){
        s.print(depth);
        //--------------------------------------Closing Rules ---------------------------------------
        
        //Base case: ID
        if(s.isClosed()){
            for(int k = 0; k < depth; k++) std::cout << "| ";
            std::cout << "Applying ID " << std::endl;
            for(int k = 0; k < depth; k++) std::cout << "| ";
            std::cout << ">>> Branch Closed (Identity)\n";
            return true;
        }

        //Limit Depth (prevent infinite loops)
        if (depth > 50) return false;

        //--------------------------------------Non-Branching Rules ---------------------------------
        
        //AND on Left
        for(size_t i = 0; i < s.antecedent.size(); ++i){
            if(s.antecedent[i]->type == NodeType::AND) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying AND_L " << std::endl;

                Sequent next = s;
                auto A = next.antecedent[i]->children[0];
                auto B = next.antecedent[i]->children[1];
                
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(A);
                next.antecedent.push_back(B);
                return prove(next, used, depth + 1);
            }
        }

        //OR on Right
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::OR) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying OR_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(A);
                next.succedent.push_back(B);
                return prove(next, used, depth + 1);
            }
        }
        
        //IMPLY on Right
        for(size_t i = 0; i < s.succedent.size(); ++i){
            if(s.succedent[i]->type == NodeType::IMPLY) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying IMPLY_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A);
                next.succedent.push_back(B);
                return prove(next, used, depth + 1);
            }
        }

        //NEGATION on Left
        for (size_t i = 0; i < s.antecedent.size(); i++) {
            if(s.antecedent[i]->type == NodeType::NOT) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying NEGATE_L " << std::endl;
                Sequent next = s;
                auto A = next.antecedent[i]->children[0];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.succedent.push_back(A); //Move A to right
                return prove(next, used, depth + 1);
            }
        }

        //NEGATION on Right 
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::NOT) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying NEGATE_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A); //Move A to left
                return prove(next, used, depth + 1);
            }
        }

        //FORALL Right
        for(size_t i = 0; i < s.succedent.size(); ++i) {
            if(s.succedent[i]->type == NodeType::FORALL) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying FORALL_R " << std::endl;
                std::string termToUse = getFreshTerm();
                Sequent next = s;
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];

                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(substitute(body, varName, termToUse));
                return prove(next, used, depth + 1);
            }
        }
        
        //EXISTS on Left
        for(size_t i = 0; i < s.antecedent.size(); ++i) {
            if(s.antecedent[i]->type == NodeType::EXISTS) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying EXISTS_L " << std::endl;
    
                std::string termToUse = getFreshTerm();
                Sequent next = s;
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];

                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(substitute(body, varName, termToUse));
                return prove(next, used, depth + 1);
            }
        }        


        //--------------------------------------Branching Rules--------------------------------------
        
        //AND on Right
        for (size_t i = 0; i < s.succedent.size(); i++){
            if(s.succedent[i]->type == NodeType::AND){
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "==> Branching: Applying AND_R " << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;

                auto A = s.succedent[i]->children[0];
                auto B = s.succedent[i]->children[1];

                leftBranch.succedent.erase(leftBranch.succedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.succedent.erase(rightBranch.succedent.begin() + i);
                rightBranch.succedent.push_back(B);
               
                bool leftSuccess = prove(leftBranch, used, depth + 1);
                if (leftSuccess){
                    for(int k = 0; k < depth; k++) std::cout << "| ";
                    std::cout << "--- Left Branch Closed, checking Right Branch ---" << std::endl;
                    return prove(rightBranch, used, depth + 1);
                }
                return false;
            }
        }
        
        //OR on Left
        for (size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::OR){
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "==> Branching: Applying OR_L " << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;
                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];

                leftBranch.antecedent.erase(leftBranch.antecedent.begin() + i);
                leftBranch.antecedent.push_back(A);

                rightBranch.antecedent.erase(rightBranch.antecedent.begin() + i);
                rightBranch.antecedent.push_back(B);

                
                bool leftSuccess = prove(leftBranch, used, depth + 1);
                if (leftSuccess){
                    for(int k = 0; k < depth; k++) std::cout << "| ";
                    std::cout <<  "--- Left Branch Closed, checking Right Branch ---" << std::endl;
                    return prove(rightBranch, used, depth + 1);
                }
                return false;
            }
        }

        //IMPLY on Left
        for (size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::IMPLY){
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "==> Branching: Applying IMPLY_L " << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;

                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];

                leftBranch.antecedent.erase(leftBranch.antecedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.antecedent.erase(rightBranch.antecedent.begin() + i);
                rightBranch.antecedent.push_back(B);

                bool leftSuccess = prove(leftBranch, used, depth + 1);
                if (leftSuccess){
                    for(int k = 0; k < depth; k++) std::cout << "| ";
                    std::cout << "--- Left Branch Closed, checking Right Branch ---" << std::endl;
                    return prove(rightBranch, used, depth + 1);
                }
                return false;
            }
        }

        //------------------------------------------------------------------------------------------
        //FORALL Left
        for(size_t i = 0; i < s.antecedent.size(); i++) {
            if (s.antecedent[i]->type == NodeType::FORALL){
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying FORALL_L " << std::endl;
                
                auto terms = s.getExistingTerms();
                std::string termToUse = "";

                for(const auto& t : terms){
                    if (used[s.antecedent[i]].find(t) == used[s.antecedent[i]].end()){
                        termToUse = t;
                        break;
                    }
                }

                if(termToUse == ""){
                    termToUse = getFreshTerm();
                }
                used[s.antecedent[i]].insert(termToUse);

                Sequent next = s;
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];
                auto substituted = substitute(body, varName, termToUse);
                next.antecedent.push_back(substituted);

                auto quantifier = next.antecedent[i];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(quantifier);

                return prove(next, used, depth + 1);
            }
        }

        //EXISTS Right
        for(size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::EXISTS){
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Applying EXISTS_R " << std::endl;
                auto terms = s.getExistingTerms();
                std::string termToUse = "";

                for(const auto& t : terms){
                    if (used[s.succedent[i]].find(t) == used[s.succedent[i]].end()){
                        termToUse = t;
                        break;
                    }
                }

                if(termToUse == ""){
                    termToUse = getFreshTerm();
                }
                used[s.succedent[i]].insert(termToUse);
                
                
                Sequent next = s;
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];

                next.succedent.push_back(substitute(body, varName, termToUse));

                auto quantifier = next.succedent[i];
                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(quantifier);

                return prove(next, used , depth + 1);
            }
        }
        
        //EQUIVALENT on Right
        for(size_t i = 0; i < s.succedent.size(); i++){
            if(s.succedent[i]->type == NodeType::EQUIV) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Expanding EQUIVALENT_R " << std::endl;
                Sequent next = s;
                auto A = s.succedent[i]->children[0];
                auto B = s.succedent[i]->children[1];
                //create (a -> b) & (b -> a)
                auto imp1 = std::make_shared<Node>(NodeType::IMPLY, A, B);
                auto imp2 = std::make_shared<Node>(NodeType::IMPLY, B, A);
                auto combined = std::make_shared<Node>(NodeType::AND, imp1, imp2);

                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(combined);
                return prove(next, used, depth + 1);
            }
        }

        //EQUIVALENT on Left
        for(size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::EQUIV) {
                for(int k = 0; k < depth; k++) std::cout << "| ";
                std::cout << "Expanding EQUIVALENT_L " << std::endl;
                Sequent next = s;
                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];
                //create (a -> b) & (b -> a)
                auto imp1 = std::make_shared<Node>(NodeType::IMPLY, A, B);
                auto imp2 = std::make_shared<Node>(NodeType::IMPLY, B, A);
                auto combined = std::make_shared<Node>(NodeType::AND, imp1, imp2);

                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(combined);
                return prove(next, used, depth + 1);
            }
        }
        
   



        return false; //no rules to close branch
    }

    //Helper for substitution
    std::shared_ptr<Node> substitute(std::shared_ptr<Node> node, const std::string& var, const std::string& term) {
        if(!node) return nullptr;
        //If its the variable we are looking for, replace it
        if(node->type == NodeType::ATOM && node->name == var && node->children.empty()){
            return std::make_shared<Node>(NodeType::ATOM, term);
        }
        //Otherwise clone the node and recurse on children
        auto newNode = std::make_shared<Node>(node->type, node->name);
        for (auto& child : node->children) {
            newNode->children.push_back(substitute(child, var, term));
        }
        return newNode;
    }        
};

//-----------------------------------------------------------------------------
int main(){
 
    // read input
    std::string tptpTest = "fof(test, conjecture, (p(a) & ![X] : (p(X) => q(X))) => q(a)).";
    
    //1. lexing 
    Lexer lexer(tptpTest);
    std::vector<Token> tokens;
    Token t;
    std::shared_ptr<Node> root;
    try {
        do {
            t = lexer.nextToken();
            tokens.push_back(t);
        } while (t.type != Token::END);
    } catch (const std::exception& e) {
        std::cerr << "Lexer Error: " << e.what() << std::endl;
        return 1;
    }
    //2. parsing 
    try {
        Parser parser(tokens);
        root = parser.parseTopLevel();
        
        std::cout << "--- ASCII Visualisation ---\n";

    } catch (const std::exception& e) {
        std::cerr << "Parser Error: " << e.what() << std::endl;
        return 1;
    }
    
    //3. Algorithm 2
    Sequent initial;
    initial.succedent.push_back(root); //prove formula as conjecture

    Prover::UsedRegistry used;
    Prover prover;
    if (prover.prove(initial, used, 0)) {
        std::cout << "Success: Theorem Proved! \n";
    } else {
        std::cout << "Failure: Could not find proof.\n";
    }

    return 0;
}
