#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <set>
#include <functional>
#include <map>
#include <fstream>
#include <chrono>


//--------------------------------BENCHMARKING------------------------------------

struct Stats {
    int nodesExplored = 0;
    int peakDepth = 0;
};

struct Result {
    std::string problem;
    bool proved;
    double timeMs;
    int nodes;
    int peakDepth;
};

/*
void writeCSV(const std::vector<Result>& improved,
              const std::string& filename) {
    
                std::ofstream out(filename);
    // Header
    out << "Problem,"
        << "Improved Result,Improved Time(ms),Improved Nodes,Improved PeakDepth\n";

    for (size_t i = 0; i < improved.size(); i++) {
        const auto& b = improved[i];
        
        out << "\"" << b.problem << "\","
            << (b.proved  ? "Proved" : "Failed") << "," << b.timeMs  << "," << b.nodes  << "," << b.peakDepth << "\n";
    }
    std::cout << "CSV written to: " << filename << std::endl;
}
*/
//----------------------------------PARSER-------------------------------------

enum class NodeType {
    ATOM, NOT, AND, OR, IMPLY, FORALL, EXISTS
};

struct Node {
    NodeType type;
    std::string name; //for predicate names or variables
    std::vector<std::shared_ptr<Node>> children;
    std::set<std::string> usedTerms;
    int size() const {
        int count = 1;
        for (const auto& child: children){
            count += child->size();
        }
        return count;
    }

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

        if (op != ""){
            return "(" + children[0]->toString() + op + children[1]->toString() + ")";
        }

        if (type == NodeType::FORALL) return "![ " + name + " ] : " + children[0]->toString();
        if (type == NodeType::EXISTS) return "?[ " + name + " ] : " + children[0]->toString();

        return "???";
    }

};

//Lexer

struct Token {
    enum Type{
        FOF, LPAREN, RPAREN, LBRACKET, RBRACKET, COMMA, PERIOD, COLON,
        NOT, AND, OR, IMPLY, FORALL, EXISTS, ID, VAR, END}; 
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
    
        if (isdigit(input[pos])) {
            std::string val;
            while (pos < input.length() && isdigit(input[pos])) {
                val += input[pos++];
            }
            return {Token::ID, val}; // Treat numbers as IDs for simplicity
        }

        if(pos < input.length() && input[pos] == '%') {
            while(pos < input.length() && input[pos] != '\n') pos++;
            return nextToken(); // recurse to get the next real token
        }

        //check multi-char symbols
        if(pos + 1 < input.length() && input.substr(pos, 2) == "=>"){
            pos += 2;
            return {Token::IMPLY, "=>" };
        }

        if(pos < input.length() && input[pos] == '$') {
            pos++; // consume $
            std::string value = "";
            while (pos < input.length() && (isalnum(input[pos]) || input[pos] == '_')) {
                value += input[pos++];
            }
        return {Token::ID, value}; // returns "false" or "true" as a plain ID
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
    //Node(NodeType t);
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
        while (peek().type == Token::IMPLY) {
            Token op = advance();
            auto right = parseDisjunction();
            left = std::make_shared<Node>(NodeType::IMPLY, left, right);
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
 
    std::shared_ptr<Node> buidNestedQuantifier(NodeType type, std::vector<std::string>& vars, std::shared_ptr<Node> body) {
        for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
            body = std::make_shared<Node>(type, *it, body);
        }
        return body;
    }
    std::shared_ptr<Node> parseTopLevel(std::string& outRole) {
        match(Token::FOF); 
        match(Token::LPAREN);
        
        if (peek().type == Token::ID || peek().type == Token::VAR) advance();
        match(Token::COMMA);
        
        Token roleTok = match(Token::ID); 
        outRole = roleTok.value;
        match(Token::COMMA);

        auto formula = parseFormula();

        match(Token::RPAREN); 
        match(Token::PERIOD);
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
    bool isAtEnd() const {
        return tokens[current].type == Token::END;
    }
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
            if (n->type == NodeType::ATOM && !n->children.empty()) {
                for( auto& child : n->children) {
                    if(child->type == NodeType::ATOM && child->children.empty()){
                        if (!child->name.empty() && islower(child->name[0])) {
                            terms.insert(child->name);
                        }
                    }
                }
            }
            for (auto& child : n->children) find(child);
        };
        for (auto& f : antecedent) find(f);
        for (auto& f : succedent) find(f);
        return terms;
    }

    std::shared_ptr<Node> pushNegation(std::shared_ptr<Node> node) {
        if (!node) return nullptr;

        if (node->type == NodeType::NOT) {
            auto child = node->children[0];

            // ~~A → A
            if (child->type == NodeType::NOT) {
                return pushNegation(child->children[0]);
            }

            // ¬(A ∧ B) → ¬A ∨ ¬B
            if (child->type == NodeType::AND) {
                auto leftNot = std::make_shared<Node>(NodeType::NOT, child->children[0]);
                auto rightNot = std::make_shared<Node>(NodeType::NOT, child->children[1]);
                return std::make_shared<Node>(NodeType::OR,
                    pushNegation(leftNot),
                    pushNegation(rightNot));
            }

            // ¬(A ∨ B) → ¬A ∧ ¬B
            if (child->type == NodeType::OR) {
                auto leftNot = std::make_shared<Node>(NodeType::NOT, child->children[0]);
                auto rightNot = std::make_shared<Node>(NodeType::NOT, child->children[1]);
                return std::make_shared<Node>(NodeType::AND,
                    pushNegation(leftNot),
                    pushNegation(rightNot));
            }

            // ¬∀X A → ∃X ¬A
            if (child->type == NodeType::FORALL) {
                auto negBody = std::make_shared<Node>(NodeType::NOT, child->children[0]);
                return std::make_shared<Node>(NodeType::EXISTS, child->name, pushNegation(negBody));
            }

            // ¬∃X A → ∀X ¬A
            if (child->type == NodeType::EXISTS) {
                auto negBody = std::make_shared<Node>(NodeType::NOT, child->children[0]);
                return std::make_shared<Node>(NodeType::FORALL, child->name, pushNegation(negBody));
            }
        }

        // default: recurse
        auto newNode = std::make_shared<Node>(node->type, node->name);
        for (auto& c : node->children) {
            newNode->children.push_back(pushNegation(c));
        }
        return newNode;
    }

    std::shared_ptr<Node> eliminateImplications(std::shared_ptr<Node> node) {
        if (!node) return nullptr;

        if (node->type == NodeType::IMPLY) {
            auto notA = std::make_shared<Node>(NodeType::NOT, eliminateImplications(node->children[0]));
            return std::make_shared<Node>(NodeType::OR, notA, eliminateImplications(node->children[1]));
        }

        auto newNode = std::make_shared<Node>(node->type, node->name);
        for (auto& c : node->children) {
            newNode->children.push_back(eliminateImplications(c));
        }
        return newNode;
    }

    void normalise() {
    for (auto& f : antecedent) {
        f = eliminateImplications(f);
        f = pushNegation(f);
    }
    for (auto& f : succedent) {
        f = eliminateImplications(f);
        f = pushNegation(f);
    }
}
    bool hasNegatedQuantifier(std::shared_ptr<Node> node) {
        if (!node) return false;
        if (node->type == NodeType::NOT && !node->children.empty()) {
            auto child = node->children[0];
            if (child->type == NodeType::FORALL || child->type == NodeType::EXISTS)
                return true;
        }
        for (auto& c : node->children)
            if (hasNegatedQuantifier(c)) return true;
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
    using UsedRegistry = std::map<std::shared_ptr<Node>, std::set<std::string>>;
    bool prove(Sequent s, UsedRegistry used, Stats& stats, int depth = 0){
        //--------------------------------------Closing Rules ---------------------------------------
            
  //  std::cout << "Checking closure - Antecedent atoms: ";
 //   for (auto& f : s.antecedent) {
 //       if (f->type == NodeType::ATOM)
 //           std::cout << "'" << f->name << "'(children:" << f->children.size() << ") ";
 //   }
 //   std::cout << "\nSuccedent atoms: ";
 //   for (auto& f : s.succedent) {
 //       if (f->type == NodeType::ATOM)
 //           std::cout << "'" << f->name << "'(children:" << f->children.size() << ") ";
 //   }
//std::cout << std::endl;


        stats.nodesExplored++;
        
        stats.peakDepth = std::max(stats.peakDepth, depth);
        //Base case: ID
        if(s.isClosed()){
     //       std::cout << "CLOSED via ID" << std::endl;
            return true;
        }

        // Base case: BOTTOM_L (false on the left closes the branch)
        for (const auto& a : s.antecedent) {
            if (a->type == NodeType::ATOM && a->name == "false") return true;
        }

        //Limit Depth (prevent infinite loops)
        if (depth > 1000) return false;

        //if (stats.nodesExplored > 800000) return false;

        //--------------------------------------Non-Branching Rules ---------------------------------
        
        //AND on Left
        for(size_t i = 0; i < s.antecedent.size(); ++i){
            if(s.antecedent[i]->type == NodeType::AND) {
                
            //    std::cout << "Applying AND_L" << std::endl;
            //    std::cout << "Antecedent: ";
             //   for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
             //   std::cout << "\nSuccedent: ";
            //    for (auto& f : s.succedent) std::cout << f->toString() << " | ";
            //    std::cout << std::endl;
                
                Sequent next = s;
                auto A = next.antecedent[i]->children[0];
                auto B = next.antecedent[i]->children[1];
                
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(A);
                next.antecedent.push_back(B);
                
                return prove(next, used, stats, depth + 1);
            }
        }
        //OR on Right
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::OR) {
                
           //     std::cout << "Applying OR_R" << std::endl;
           //     std::cout << "Antecedent: ";
           //     for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
            //    std::cout << "\nSuccedent: ";
            //    for (auto& f : s.succedent) std::cout << f->toString() << " | ";
            //    std::cout << std::endl;
                
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
               
                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(A);
                next.succedent.push_back(B);
                
                return prove(next, used, stats, depth + 1);
            }
        }
        //IMPLY on Right
        for(size_t i = 0; i < s.succedent.size(); ++i){
            if(s.succedent[i]->type == NodeType::IMPLY) {

             //   std::cout << "Applying IMPLY_R" << std::endl;
              //  std::cout << "Antecedent: ";
              //  for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
              //  std::cout << "\nSuccedent: ";
             //   for (auto& f : s.succedent) std::cout << f->toString() << " | ";
             //   std::cout << std::endl;
                
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
                auto B = next.succedent[i]->children[1];
                
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A);
                next.succedent.push_back(B);
                
                return prove(next, used, stats, depth + 1);
            }
        }
        //NEGATION on Left
        for (size_t i = 0; i < s.antecedent.size(); i++) {
            if(s.antecedent[i]->type == NodeType::NOT) {

              //  std::cout << "Applying NEGATION_L" << std::endl;
              //  std::cout << "Antecedent: ";
              //  for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
             //   std::cout << "\nSuccedent: ";
              //  for (auto& f : s.succedent) std::cout << f->toString() << " | ";
             //   std::cout << std::endl;
                
                Sequent next = s;
                auto A = next.antecedent[i]->children[0];
              
                next.antecedent.erase(next.antecedent.begin() + i);
                next.succedent.push_back(A); //Move A to right
              
                return prove(next, used, stats, depth + 1);
            }
        }
        //NEGATION on Right 
        for (size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::NOT) {
               // std::cout << "Applying NEGATION_R" << std::endl;
                //std::cout << "Antecedent: ";
               // for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
               // std::cout << "\nSuccedent: ";
               // for (auto& f : s.succedent) std::cout << f->toString() << " | ";
               // std::cout << std::endl;
                
                Sequent next = s;
                auto A = next.succedent[i]->children[0];
               
                next.succedent.erase(next.succedent.begin() + i);
                next.antecedent.push_back(A); //Move A to left
               
                return prove(next, used, stats, depth + 1);
            }
        }
        //FORALL Right
        for(size_t i = 0; i < s.succedent.size(); ++i) {
            if(s.succedent[i]->type == NodeType::FORALL) {
                //std::cout << "Applying FORALL_R" << std::endl;
                //std::cout << "Antecedent: ";
                //for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
               // std::cout << "\nSuccedent: ";
                //for (auto& f : s.succedent) std::cout << f->toString() << " | ";
                //std::cout << std::endl;

                std::string termToUse = getFreshTerm();
                Sequent next = s;
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];

                next.succedent.erase(next.succedent.begin() + i);
                next.succedent.push_back(substitute(body, varName, termToUse));
               
                return prove(next, used, stats, depth + 1);
            }
        }
        //EXISTS on Left
        for(size_t i = 0; i < s.antecedent.size(); ++i) {
            if(s.antecedent[i]->type == NodeType::EXISTS) {      
                std::string termToUse = getFreshTerm();
                //std::cout << "Applying EXISTS_L" << std::endl;
                //std::cout << "Antecedent: ";
                //for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
                //std::cout << "\nSuccedent: ";
                //for (auto& f : s.succedent) std::cout << f->toString() << " | ";
                //std::cout << std::endl;

                Sequent next = s;
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];

                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(substitute(body, varName, termToUse));
              
                return prove(next, used, stats, depth + 1);
            }
        }        
       

        //--------------------------------------Branching Rules--------------------------------------
        
        //AND on Right
        for (size_t i = 0; i < s.succedent.size(); i++){
            if(s.succedent[i]->type == NodeType::AND){
                Sequent leftBranch = s;
                Sequent rightBranch = s;
                auto A = s.succedent[i]->children[0];
                auto B = s.succedent[i]->children[1];
    //            std::cout << "Applying AND_R" << std::endl;
    //            std::cout << "Antecedent: ";
    //            for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
     //           std::cout << "\nSuccedent: ";
      //          for (auto& f : s.succedent) std::cout << f->toString() << " | ";
      //          std::cout << std::endl;

                if (A->size() > B->size()) std::swap(A, B);

                leftBranch.succedent.erase(leftBranch.succedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.succedent.erase(rightBranch.succedent.begin() + i);
                rightBranch.succedent.push_back(B);
               
                bool leftSuccess = prove(leftBranch, used, stats, depth + 1);
                if (leftSuccess){
                    return prove(rightBranch, used, stats, depth + 1);
                }
               
                return false;
            }
        }
        
        //OR on Left
        {
        int bestIdx = -1;
        int bestScore = INT_MAX;
        for (size_t i = 0; i < s.antecedent.size(); i++) {
            if (s.antecedent[i]->type == NodeType::OR) {
                int score = s.antecedent[i]->size();
                if (score < bestScore) {
                    bestScore = score;
                    bestIdx = i;
                }
            }
        }
        if (bestIdx >= 0) {
  //          std::cout << "Applying OR_L" << std::endl;
  //          std::cout << "Antecedent: ";
  //          for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
   //         std::cout << "\nSuccedent: ";
   //         for (auto& f : s.succedent) std::cout << f->toString() << " | ";
    //        std::cout << std::endl;
            Sequent leftBranch = s;
            Sequent rightBranch = s;
            auto A = s.antecedent[bestIdx]->children[0];
            auto B = s.antecedent[bestIdx]->children[1];

            if (A->size() > B->size()) std::swap(A, B);

            leftBranch.antecedent.erase(leftBranch.antecedent.begin() + bestIdx);
            leftBranch.antecedent.push_back(A);

            rightBranch.antecedent.erase(rightBranch.antecedent.begin() + bestIdx);
            rightBranch.antecedent.push_back(B);

            bool leftSuccess = prove(leftBranch, used, stats, depth + 1);
            if (leftSuccess) {
                return prove(rightBranch, used, stats, depth + 1);
            }
            return false;
        }
        }
    
        //IMPLY on Left
        for (size_t i = 0; i < s.antecedent.size(); i++){
            if(s.antecedent[i]->type == NodeType::IMPLY){
                Sequent leftBranch = s;
                Sequent rightBranch = s;

                auto A = s.antecedent[i]->children[0];
                auto B = s.antecedent[i]->children[1];

                leftBranch.antecedent.erase(leftBranch.antecedent.begin() + i);
                leftBranch.succedent.push_back(A);

                rightBranch.antecedent.erase(rightBranch.antecedent.begin() + i);
                rightBranch.antecedent.push_back(B);

                bool leftSuccess = prove(leftBranch, used, stats, depth + 1);
                bool rightSuccess = prove(rightBranch, used, stats, depth + 1);
     //           std::cout << "IMPLY_L results: left=" << leftSuccess << " right=" << rightSuccess << std::endl;
                if (leftSuccess && rightSuccess) return true;
                return false;
            }
        }

        //------------------------------------------------------------------------------------------
        // EXISTS-R: instantiate with existing unused term
        for(size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::EXISTS){
       //         std::cout << "Applying EXISTS_R (existing unused term)" << std::endl;
        //        std::cout << "Antecedent: ";
         //       for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
          //      std::cout << "\nSuccedent: ";
          //      for (auto& f : s.succedent) std::cout << f->toString() << " | ";
          //      std::cout << std::endl;

                auto terms = s.getExistingTerms();
                std::string termToUse = "";

                for(const auto& t : terms){
                    if (used[s.succedent[i]].find(t) == used[s.succedent[i]].end()){
                        termToUse = t;
                        break;
                    }
                }
                if (termToUse == "") continue;

                used[s.succedent[i]].insert(termToUse);
                Sequent next = s;
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];
                next.succedent.erase(next.succedent.begin() + i); // remove quantifier
                next.succedent.push_back(substitute(body, varName, termToUse)); // add instance only
                return prove(next, used, stats, depth + 1);
            }
        }

        // EXISTS-R: fresh term as last resort
        for(size_t i = 0; i < s.succedent.size(); i++) {
            if(s.succedent[i]->type == NodeType::EXISTS){
                std::cout << "Applying EXISTS_R (fresh)" << std::endl;
                std::cout << "Antecedent: ";
                for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
                std::cout << "\nSuccedent: ";
                for (auto& f : s.succedent) std::cout << f->toString() << " | ";
               std::cout << std::endl;

                if(used[s.succedent[i]].size() >= 3) return false;
                std::string termToUse = getFreshTerm();
                used[s.succedent[i]].insert(termToUse);
                Sequent next = s;
                std::string varName = next.succedent[i]->name;
                auto body = next.succedent[i]->children[0];
                next.succedent.erase(next.succedent.begin() + i); // remove quantifier
                next.succedent.push_back(substitute(body, varName, termToUse)); // add instance only
                return prove(next, used, stats, depth + 1);
            }
        }
        
        //FORALL Left
        for(size_t i = 0; i < s.antecedent.size(); i++) {
            if (s.antecedent[i]->type == NodeType::FORALL){

                auto terms = s.getExistingTerms();
                std::string termToUse = "";
               
                for(const auto& t : terms){
                    if (used[s.antecedent[i]].find(t) == used[s.antecedent[i]].end()){
                        termToUse = t;
                        break;
                    }
                }
                if (termToUse == "") continue; // no unused term, skip for now

                used[s.antecedent[i]].insert(termToUse);
                Sequent next = s;
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];
                next.antecedent.push_back(substitute(body, varName, termToUse));
                auto quantifier = next.antecedent[i];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(quantifier);
                return prove(next, used, stats, depth + 1);
            }
        }

        // FORALL-L: no unused terms exist, create a fresh term (last resort)
        for(size_t i = 0; i < s.antecedent.size(); i++) {
            if (s.antecedent[i]->type == NodeType::FORALL){
               std::cout << "Applying FORALL_L (fresh)" << std::endl;
                std::cout << "Antecedent: ";
                for (auto& f : s.antecedent) std::cout << f->toString() << " | ";
                std::cout << "\nSuccedent: ";
               for (auto& f : s.succedent) std::cout << f->toString() << " | ";
                std::cout << std::endl;

                //if(used[s.antecedent[i]].size() >= 1000) continue;
                std::string termToUse = getFreshTerm();
                used[s.antecedent[i]].insert(termToUse);
                Sequent next = s;
                std::string varName = next.antecedent[i]->name;
                auto body = next.antecedent[i]->children[0];
                next.antecedent.push_back(substitute(body, varName, termToUse));
                auto quantifier = next.antecedent[i];
                next.antecedent.erase(next.antecedent.begin() + i);
                next.antecedent.push_back(quantifier);
                return prove(next, used, stats, depth + 1);
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


//--------------------------------MAIN_FUNCTION------------------------------------

int main(int argc, char* argv[]) {
    if (argc < 2){
        std::cerr << "Usage: " << argv[0] << " <tptp_file_path>" << std::endl;
        return 1;
    }

    std::ifstream file(argv[1]);
    if (!file.is_open()) {
        std::cerr << "Error: Could not open file " << argv[1] << std::endl;
        return 1;
    }

    std::string line, content;
    Sequent initial;

    while (std::getline(file, line)){
        if(line.empty() || line[0] == '%') continue;
        content += line + "\n"; // ← preserve newlines so inline % comments terminate
    }

    Lexer lexer(content);
    std::vector<Token> tokens;
    try {
        Token t;
        do {
            t = lexer.nextToken();
            tokens.push_back(t);
        } while (t.type != Token::END);
    } catch (const std::exception& e) {
        std::cerr << "Lexer Error: " << e.what() << std::endl;
        return 1;
    }
    int testCount = 0;
    int successCount = 0;
    try {
        Parser parser(tokens);
        while (!parser.isAtEnd()) {
            std::string role;
            std::shared_ptr<Node> formula = parser.parseTopLevel(role);
            
            if (!formula) continue;
            
            if(formula){
                if (role == "axiom" || role == "hypothesis") {
                    initial.antecedent.push_back(formula);
                } else if (role == "conjecture") {
                    initial.succedent.push_back(formula);
                } else {
                    initial.antecedent.push_back(formula);
                }
                //std::cout << "Parsed " << role << " successfully." << std::endl;
            }
        }
        //std::cout << "Total Axioms: " << initial.antecedent.size() << std::endl;
    } catch (const std::exception& e) {
        std::cerr << "Parser Error: " << e.what() << std::endl;
        return 1;
    }
    std::vector<std::string> failedProblems;
    auto global_start = std::chrono::high_resolution_clock::now();
    auto global_nodes = 0;
    auto problem_counter = 0;
    auto proven = 0;
    auto failed = 0;

    std::cout << "--- Starting Proof Search ---" << std::endl;
    std::vector<std::shared_ptr<Node>> axioms;
    std::vector<Result> improvedResults;
    for (auto& f: initial.antecedent){
        axioms.push_back(f);
    }

        for (auto& conjecture : initial.succedent) {
        Sequent s;
        s.antecedent = axioms;
        s.succedent.push_back(conjecture);
        
        Stats stats;
        Prover::UsedRegistry used;
        Prover prover;
        std::string problemStr = conjecture->toString();    
        std::cout << "\nProving: " << problem_counter << " " << problemStr << std::endl;
        
        auto start = std::chrono::high_resolution_clock::now();
        for (auto& f : s.antecedent)
            if (s.hasNegatedQuantifier(f)) f = s.pushNegation(s.eliminateImplications(f));
        for (auto& f : s.succedent)
           if (s.hasNegatedQuantifier(f)) f = s.pushNegation(s.eliminateImplications(f));
        
        bool result = prover.prove(s, used, stats, 0);
        problem_counter += 1;
        if(result){ 
            proven += 1;
        } else {  
            failed += 1;
            failedProblems.push_back(conjecture->toString().substr(0, 80));
        }
        auto end = std::chrono::high_resolution_clock::now();

        double ms = std::chrono::duration<double, std::milli>(end - start).count();

        //std::cout << "Result:       " << (result ? "Proved" : "Failed") << std::endl;
        //std::cout << "Time:         " << ms << " ms" << std::endl;
        //std::cout << "Nodes:        " << stats.nodesExplored << std::endl;
        //std::cout << "Peak depth:   " << stats.peakDepth << std::endl;
        global_nodes += stats.nodesExplored;
        improvedResults.push_back({problemStr, result, ms, stats.nodesExplored, stats.peakDepth});
    }
    
    auto global_end = std::chrono::high_resolution_clock::now();
    std::cout << "--- Proof Search Concluded --- " << std::endl;
    double global_ms = std::chrono::duration<double, std::milli>(global_end - global_start).count();
    std::cout << "Number of Problems Attempted:     " << problem_counter << std::endl;
    std::cout << "Proven:                           " << proven << std::endl; 
    std::cout << "Failed:                           " << failed << std::endl;
    std::cout << "Total Time:                       " << global_ms << " ms" << std::endl;
    std::cout << "Average Time to solve:            " << (global_ms / problem_counter) << " ms" << std::endl;
    std::cout << "Average Number of Nodes Explored: " << (global_nodes / problem_counter) << std::endl;
    

    if (!failedProblems.empty()) {
    std::cout << "\nFailed Problems:" << std::endl;
    for (const auto& name : failedProblems) {
        std::cout << "  - " << name << std::endl;
    }
}
    
    return 0;
}
