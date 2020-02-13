/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
using namespace std;
//#define DEBUG
// Global Variables for storing finalAssignment and totalNumberofClauses and Variables
vector<bool>finalAssignment;
int totalClauses,totalVariables; // These are initialized in main()
/**
 * Class for representing a Clause in the input
 */
class clause{
    private:
        bool tautology=false; // This is true when a clause contains a literal and its negation.
        int totalLiterals=0;  // Count of total number of literals in the clause
    public:
        vector<int>literals;  // This vector stores all the literals 
        clause(){}            // default constructor
        // Create a clause object with one literal 
        clause(int unitLiteral){
            literals.emplace_back(unitLiteral); // emplace_back is faster than push_back
        }
        /**
        * addLiteral function adds a literal to the clause
        * while adding it increments the totalLiterals
        * and also checks for its negated literal, if it
        * finds it it sets tautology to true
        * positive literal are represented by even numbers +1->2,+2->4,...
        * negative literal are represented by odd numbers -1->1,-2->3,...
        */

        inline void addLiteral(int x){
            totalLiterals++;
            if(x<0){
                // convert negative literal to corresponding odd number
                literals.emplace_back(-2*x-1);
                tautology|=(find(literals.begin(),literals.end(),2*x)!=literals.end()); // bitwise or 
            }
            else{
                // convert positive literal to corresponding even number
                literals.emplace_back(2*x);
                tautology|=(find(literals.begin(),literals.end(),-2*x-1)!=literals.end());
            }
        }
        // Returns total Literals
        int getCountLiteralsInClause(){
            return totalLiterals;
        }
        // Returns whether clause is a tautology
        bool isTautology(){
            return tautology;
        }
};
/**
 * class clauseSetCurrentState
 * It maintains state of the clauses 
 * It stores count of unsatified literals in each clause,
 * whether a clause is satisfied and 
 * stores literals of clauses that are UnitClauses.(clauses containing only one unsatisfied literal)
 * Count of each literal in clauses
 */
class clauseSetCurrentState{
    public:
        vector <bool> issatisfied;
        vector <int> unitLiterals;  // stores literals of all unitClauses for unitPropogation
    clauseSetCurrentState(){        // default constructor
        issatisfied.emplace_back(false);
    }
    clauseSetCurrentState(const clauseSetCurrentState& state){  // copy constructor
        issatisfied=state.issatisfied;
        unitLiterals=state.unitLiterals;
    }
};
/**
 * Clause clauseSet
 * Stores all the clauses information
 */
class clauseSet{
    public:
        vector <clause> clauses; // vector of clause
        // for each literal we keep a pointer to a list(vector) which stores in which clauses it occurs.
        vector<unordered_set<int>*> literalClauseMap;  
        vector<pair<int,int>>watchedLit;  
        // state stores the initial state of all the clauses
        clauseSetCurrentState state;
        clauseSet(){                 
            // clauses are also 1 indexed put a dummy clause at 0 index
            clauses.emplace_back(clause(0));  
            watchedLit.push_back({-1,-1});
            // push the pointer's of list to the literalClauseMap                 
            for(int i=0;i<2*totalVariables+5;i++)
                literalClauseMap.push_back(new unordered_set<int>());           
        }
        /**
         * Add clause method add a clause to the clauseset only if it not
         * a tautology. It then updates countClause and the literalClauseMap
         */
        void addClause(clause cs){
            if(cs.isTautology())
                return;
            else{
                state.issatisfied.emplace_back(false);
                clauses.emplace_back(cs); // add to clauses
                if(cs.literals.size() == 1){ // It is a unit Clause
                    state.unitLiterals.emplace_back(cs.literals.front());
                    watchedLit.push_back({0,0});
                }
                else{
                    auto it=cs.literals.begin();
                    watchedLit.push_back({0,cs.literals.size()-1});
                    literalClauseMap[*it]->insert(clauses.size()-1);
                    it=(--cs.literals.end());
                    literalClauseMap[*it]->insert(clauses.size()-1);
                }
            }
        }
        /**
         * Pure Literal Elimination 
         * Cannot be done with 2 watched literals
         */
        // helper function to print all the indices where this literal occurs
        void printLiteral(int lit){
            cout<<lit<<" : ";
            for(auto k:(*literalClauseMap[lit]))
                cout<<k<<" ";
            cout<<endl;
        }
        bool isSatisfied(int clauseNum,vector<bool>&assigned){
            for(auto lit:clauses[clauseNum].literals){
                if(assigned[lit])
                    return true;
            }
            return false;
        }
};
// Given a literal return its complement literal
inline int complement(int i){
    if(i&1)
        return i+1;
    else
        return i-1;
}
// Given a literal return its variable
inline int getvariable(int i){
    return (i+1)/2;
}
/**
 * SATsolver Class
 * Stores a pointer to clauseset object to access literalMap and all the clauses  
 */
int iter=0;
class SATsolver{
    private:        
        clauseSet* clauseset; // a pointer to clauseset object
    public: 
        SATsolver(clauseSet* cs):clauseset(cs){} // constructor which takes a pointer to clauseset
        /**
         * dpll function which takes argument. All arguments are passed as refrences except
         * satisfiedClauses which is an int
         * currentState object(count of unsatisfied literal, which clauses are yet to be satisfied),
         * Current assignment of the literals and 
         * number of satisfied clauses(for termination)   
         * returns whether clause is satisfied with current state of clauses
         * and assignment to variables      
         */
        bool dpll(clauseSetCurrentState& state,vector<bool>&assigned,int satisfiedVariables){ 

            /////////////UNIT PROPOGATION STARTS/////////////////
            
            // to keep track which unitLiterals are processed            
            vector <bool> visited(2*totalVariables+5);
            for(int i=0;i<state.unitLiterals.size();i++){

                int unitLiteral=state.unitLiterals[i];
                if(visited[unitLiteral]) // if processed then continue;
                    continue;
                visited[unitLiteral]=true; // mark visited to true
                if(assigned[complement(unitLiteral)]){
                    #ifdef DEBUG
                    cout<<"fail state"<<" "<<unitLiteral<<endl;
                    #endif
                    return false;
                }
                if(assigned[unitLiteral])continue;
                assigned[unitLiteral]=true; // mark that literal set to true
                satisfiedVariables++;
                #ifdef DEBUG
                cout<<unitLiteral<<"?"<<endl;
                for(int i=1;i<=2*totalVariables;i++)
                    clauseset->printLiteral(i);
                #endif
                // Now we look at all the clauses where complement of this literal occurs   
                int compUnitLiteral=complement(unitLiteral);  
                vector <int> eraseList;
                if(clauseset->literalClauseMap[compUnitLiteral]->size()>0){  
                    // iterate over all the clauses containing complement of that literal                       
                    for(auto clauseNum:*(clauseset->literalClauseMap[compUnitLiteral])){
                        //cout<<"%%"<<endl;
                        iter++;
                        if(clauseset->isSatisfied(clauseNum,assigned))continue;
                        int idx1=clauseset->watchedLit[clauseNum].first;
                        int idx2=clauseset->watchedLit[clauseNum].second;
                        bool flag=false;
                        if(clauseset->clauses[clauseNum].literals[idx1]==compUnitLiteral){
                            for(int i=0;i<clauseset->clauses[clauseNum].literals.size();i++){
                                if(i==idx2 || i==idx1)continue;
                                if(assigned[clauseset->clauses[clauseNum].literals[i]]==false && 
                                    assigned[complement(clauseset->clauses[clauseNum].literals[i])]==false)
                                    {
                                        clauseset->watchedLit[clauseNum].first=i;
                                        clauseset->literalClauseMap[clauseset->clauses[clauseNum].literals[i]]->insert(clauseNum);
                                        eraseList.push_back(clauseNum);
                                        flag=true;
                                        break;
                                    }
                            }
                            if(!flag){
                                #ifdef DEBUG
                                cout<<clauseNum<<"$$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx2]<<endl;
                                #endif
                                state.unitLiterals.emplace_back(clauseset->clauses[clauseNum].literals[idx2]);
                            }
                        }else{
                             for(int i=0;i<clauseset->clauses[clauseNum].literals.size();i++){
                                if(i==idx2 || i==idx1)continue;
                               if(assigned[clauseset->clauses[clauseNum].literals[i]]==false && 
                                    assigned[complement(clauseset->clauses[clauseNum].literals[i])]==false)
                                    {
                                        clauseset->watchedLit[clauseNum].second=i;
                                        clauseset->literalClauseMap[clauseset->clauses[clauseNum].literals[i]]->insert(clauseNum);
                                        eraseList.push_back(clauseNum);
                                        flag=true;
                                        break;
                                    }
                            }
                            if(!flag){
                                #ifdef DEBUG
                                cout<<clauseNum<<"$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx1]<<endl;
                                #endif
                                state.unitLiterals.emplace_back(clauseset->clauses[clauseNum].literals[idx1]);
                            }
                        }                     
                    }  
                    for(auto k:eraseList){
                        clauseset->literalClauseMap[compUnitLiteral]->erase(k);
                    }
                }  
            }     
            if(satisfiedVariables==totalVariables){
                #ifdef DEBUG
                for(int i=1;i<=totalClauses;i++)
                    cout<<i<<" "<<clauseset->watchedLit[i].first<<" "<<clauseset->watchedLit[i].second<<endl;;
                #endif
                finalAssignment=assigned;

                return true;
            }
            /////////////UNIT PROPOGATION COMPLETED/////////////////
            // clear the unitLiterals list as all of them been taken care of
            state.unitLiterals.clear();    
            int temp=0;
          
            ///////////// HEURISTIC START ////////////////////////////
            /**
             * Chose among the unassigned variables that occurs the most (both positive and negated literal)
             * This way we deal with a lot of clauses most of them are satisfied and others
             * reach near unit propogation.
             * This heuristic gave the best performance over other heuristics such as
             * literal satifying shortest clauses, first unasigned literal 
             * and randomly selecting literal.             * 
             */
            // bestLiteral denotes the literal corresponding to highest valueof
            // literal+complement(literal) given by heuristic and
            // bestValue is the corresponding value for that literal
            // we then flip polarity of literal with 1/2 probablity
            int bestLiteral=0,bestValue=-1;
            for(int i=1;i<2*totalVariables;i+=2){
                if(!assigned[i] && !assigned[i+1]){ // both the literals are unassigned
                    bestLiteral=i;
                    break;
                }
            }
            if(bestLiteral==0){
                return false;
            }
            int random=rand()%2;
            // randomly choose either positive or negated literal
            // if(random%2==0)
            //     bestLiteral=complement(bestLiteral);

            ///////////// HEURISTIC ENDS ////////////////////////////

            // add the selected literal to unitLiterals
            state.unitLiterals.emplace_back(bestLiteral);
            /**
             * make a copy of current state and assigned vector   
             * all arguments are passed by refrence.
             * Doing this saves 1 copy. At each call only one copy is created
             * And this and the original are passed as refrences
             */

            // create a copy of current state
            //cout<<"?????????????????\n";
            clauseSetCurrentState duplicateState=clauseSetCurrentState(state); 
            // create a copy of assigned vector
            vector<bool>duplicateAssigned=assigned;
            // 1st DPLL call
            if(dpll(duplicateState,duplicateAssigned,satisfiedVariables))
                return true;
   
            // remove the literal that was selected earlier and instead 
            // add the negation of that literal in unitLiterals
            state.unitLiterals.pop_back();
            state.unitLiterals.emplace_back(complement(bestLiteral));
            // 2nd DPLL call
            return dpll(state,assigned,satisfiedVariables);            
        }
};
int main(){
    ios::sync_with_stdio(0);cin.tie(0);cout.tie(0); // fast IO
    srand(time(NULL)); // seed
    string strOneLine,str;
    int inp;
    char ch; 
    cin>>ch;
    // ignore lines starting with 'c'
    while (ch=='c'){
        getline(cin,strOneLine); 
        cin>>ch;
    }
    cin>>str>>totalVariables>>totalClauses;
    clauseSet clauses; // clauseset object
    vector<int>input; // stores literals
    while(cin>>inp){
        if(inp==0){
            clause cl;
            for(auto literal:input)
                cl.addLiteral(literal);
            clauses.addClause(cl); // add clause
            input.clear();
        }else{
            input.emplace_back(inp); // add literal
        }    
    }
    SATsolver dpllsolver(&clauses); // solver object
    vector<bool>assigned(2*totalVariables+5); // assigned vector initially all false   

    // CALL TO SOLVER
    int ret=dpllsolver.dpll(clauses.state,assigned,0); 
    cout<<ret<<" "<<iter<<endl;
    #ifdef DEBUG
    if(!ret)
        cout<<"UNSAT\n";
    else{
        cout<<"SAT\n";
        for(int i=1;i<=totalVariables*2;i+=2){
            if(finalAssignment[i])
                cout<<-1*getvariable(i)<<" ";              
            else
                cout<<getvariable(i)<<" ";     
        }
        cout<<"0\n";   
        for(auto k:clauses.clauses){
        bool set=false;
        for(auto lit: k.literals){
            if(lit==0)
                {set=true;break;}                         
            set|=finalAssignment[lit];
        }
        assert(set==true);
    }   
    }
    #endif
    return 0; 
}