#include <iostream>
#include <memory>
#include <string>
#include <vector>

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
        // Add to Node struct:
    void print(int indent = 0) const {
        // 1. Print indentation
        for (int i = 0; i < indent; ++i) std::cout << "  ";

        // 2. Print Node type and name
        std::cout << "[" << nodeTypeToString(type) << "]";
        if (!name.empty()) std::cout << ": " << name;
        std::cout << "\n";

        // 3. Recurse for children
        for (const auto& child : children) {
            if (child) child->print(indent + 1); // Step down one level
        }
    }

    // You also need this helper function:
    std::string nodeTypeToString(NodeType t) const {
        switch (t) {
            case NodeType::ATOM: return "ATOM";
            case NodeType::NOT: return "NOT";
            case NodeType::AND: return "AND";
            case NodeType::OR: return "OR";
            case NodeType::IMPLY: return "IMPLY";
            case NodeType::EQUIV: return "EQUIV";
            case NodeType::FORALL: return "FORALL";
            case NodeType::EXISTS: return "EXISTS";
            default: return "UNKNOWN";
        }
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

    //check if atom exists on both sides (ID/closure)
    bool isClosed() const {
        for (const auto& a: antecedent) {
            if(a->type != NodeType::ATOM) continue;
            for (const auto& s : succedent) {
                if (s->type == NodeType::ATOM && a->name == s->name) {
                    if(a->children.size() == s->children.size()) return true;
                }
            }
        }
        return false;
    }
};

//Prover

class Prover {
    int varCounter = 0;
    std::string getFreshTerm() {
        return "t" + std::to_string(varCounter++);
    }
public:
    bool prove(Sequent s, int depth = 0){
        
        //--------------------------------------Closing Rules ---------------------------------------
        
        //Base case: ID
        if(s.isClosed()){
            std::cout << std::string(depth, ' ') << "Applying ID " << std::endl;
            std::cout << std::string(depth, ' ') << "Branch Closed (Identity)\n";
            return true;
        }

        //Limit Depth (prevent infinite loops)
        if (depth > 20) return false;

        //--------------------------------------Non-Branching Rules ---------------------------------
        
        //NEGATION on Right 
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::NOT) {
                std::cout << std::string(depth, ' ') << "Applying NEGATE_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A); //Move A to left
                return prove(next, depth + 1);
            }
        }

        //NEGATION on Left
        for (size_t i = 0; i < s.antecedent.size(); i++) {
            if(s.antecedent[i]->type == NodeType::NOT) {
                std::cout << std::string(depth, ' ') << "Applying NEGATE_L " << std::endl;
                Sequent next = s;
                auto A = next.antecedent[i]->children[0];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.succedent.push_back(A); //Move A to right
                return prove(next, depth + 1);
            }
        }

        //OR on Right
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::OR) {
                std::cout << std::string(depth, ' ') << "Applying OR_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(A);
                next.succedent.push_back(B);
                return prove(next, depth + 1);
            }
        }
        
        
        //IMPLY on Right
        for(size_t i = 0; i < s.succedent.size(); ++i){
            if(s.succedent[i]->type == NodeType::IMPLY) {
                std::cout << std::string(depth, ' ') << "Applying IMPLY_R " << std::endl;
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A);
                next.succedent.push_back(B);
                return prove(next, depth + 1);
            }
        }
        
        //--------------------------------------Branching Rules--------------------------------------
        
        //AND on Right
        for (size_t i = 0; i < s.succedent.size(); i++){
            if(s.succedent[i]->type == NodeType::AND){
                std::cout << std::string(depth, ' ') << "Applying AND_R " << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;

                auto A = s.succedent[i]->children[0];
                auto B = s.succedent[i]->children[1];

                leftBranch.succedent.erase(leftBranch.succedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.succedent.erase(rightBranch.succedent.begin() + i);
                rightBranch.succedent.push_back(B);

                return prove(leftBranch, depth + 1) && prove(rightBranch, depth + 1);
            }
        }
        
        //OR on Left
        for (size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::OR){
                std::cout << std::string(depth, ' ') << "Applying OR_L" << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;
                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];

                leftBranch.antecedent.erase(leftBranch.antecedent.begin() + i);
                leftBranch.antecedent.push_back(A);

                rightBranch.antecedent.erase(rightBranch.antecedent.begin() + i);
                rightBranch.antecedent.push_back(B);

                return prove(leftBranch, depth + 1) && prove(rightBranch, depth + 1);
            }
        }

        //IMPLY on Left
        for (size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::IMPLY){
                std::cout << std::string(depth, ' ') << "Applying IMPLY_L " << std::endl;
                Sequent leftBranch = s;
                Sequent rightBranch = s;

                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];

                leftBranch.antecedent.erase(leftBranch.antecedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.antecedent.erase(rightBranch.antecedent.begin() + i);
                rightBranch.antecedent.push_back(B);

                return prove(leftBranch, depth + 1) && prove(rightBranch, depth + 1);        
            }
        }

        //EQUIVALENT on Right
        for(size_t i = 0; i < s.succedent.size(); i++){
            if(s.succedent[i]->type == NodeType::EQUIV) {
                std::cout << std::string(depth, ' ') << "Expanding EQUIV_R" << std::endl;
                Sequent next = s;
                auto A = s.succedent[i]->children[0];
                auto B = s.succedent[i]->children[1];
                //create (a -> b) & (b -> a)
                auto imp1 = std::make_shared<Node>(NodeType::IMPLY, A, B);
                auto imp2 = std::make_shared<Node>(NodeType::IMPLY, B, A);
                auto combined = std::make_shared<Node>(NodeType::AND, imp1, imp2);

                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(combined);
                return prove(next, depth + 1);
            }
        }

        //EQUIVALENT on Left
        for(size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::EQUIV) {
                std::cout << std::string(depth, ' ') << "Expanding EQUIV_L" << std::endl;
                Sequent next = s;
                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];
                //create (a -> b) & (b -> a)
                auto imp1 = std::make_shared<Node>(NodeType::IMPLY, A, B);
                auto imp2 = std::make_shared<Node>(NodeType::IMPLY, B, A);
                auto combined = std::make_shared<Node>(NodeType::AND, imp1, imp2);

                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(combined);
                return prove(next, depth + 1);
            }
        }
        
        //------------------------------------------------------------------------------------------
        
        //FORALL Right
        for(size_t i = 0; i < s.succedent.size(); ++i) {
            if(s.succedent[i]->type == NodeType::FORALL) {
                std::cout << std::string(depth, ' ') << "Applying FORALL_R " << std::endl;
                Sequent next = s;
                std::string fresh = getFreshTerm();
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];

                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(substitute(body, varName, fresh));
                return prove(next, depth + 1);
            }
        }
        
        //FORALL Left
        for(size_t i = 0; i < s.antecedent.size(); i++) {
            if (s.antecedent[i]->type == NodeType::FORALL){
                Sequent next = s;
                std::string term = getFreshTerm();
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];

                auto substituted = substitute(body, varName, term);
                next.antecedent.push_back(substituted);

                auto quantifier = next.antecedent[i];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(quantifier);

                return prove(next, depth + 1);
            }
        }
        
        //EXISTS  on Left
        for(size_t i = 0; i < s.antecedent.size(); ++i) {
            if(s.antecedent[i]->type == NodeType::EXISTS) {
                std::cout << std::string(depth, ' ') << "Applying EXSISTS_L " << std::endl;
                Sequent next = s;
                std::string fresh = getFreshTerm();
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];

                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(substitute(body, varName, fresh));
                return prove(next, depth + 1);
            }
        }        

        //EXISTS Right
        for(size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::EXISTS){
                std::cout << std::string(depth, ' ') << "Applying EXISTS_R" << std::endl;
                Sequent next = s;
                std::string term = getFreshTerm();
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];

                next.succedent.push_back(substitute(body, varName, term));

                auto quantifier = next.succedent[i];
                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(quantifier);

                return prove(next, depth + 1);
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
    std::string tptpTest = "fof(test, conjecture, ![X] : (p(X) => p(X))).";
    
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
        root->print();

    } catch (const std::exception& e) {
        std::cerr << "Parser Error: " << e.what() << std::endl;
        return 1;
    }
    
    //3. Algorithm 2
    Sequent initial;
    initial.succedent.push_back(root); //prove formula as conjecture

    Prover prover;
    if (prover.prove(initial)) {
        std::cout << "Success: Theorem Proved! \n";
    } else {
        std::cout << "Failure: Could not find proof.\n";
    }

    return 0;
}


