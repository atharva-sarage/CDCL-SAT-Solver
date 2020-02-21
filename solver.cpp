/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
using namespace std;
//#define DEBUG
//#define DEBUG3
//#define OUTPUT
// Global Variables for storing finalAssignment and totalNumberofClauses and Variables
struct variableState{
    int assigned,level,antClause;
};
vector<bool>finalAssignment;
vector<int>unitLiterals;
vector <variableState> state;
vector <int> depth;
int totalClauses,totalVariables; // These are initialized in main()
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
        static clause resolution(clause a,clause b,int literal){
            vector<bool> visited(2*totalVariables);
            clause newClause;
            for(auto lit:a.literals){
                visited[lit]=true;
                if(lit==literal || lit == complement(literal))
                    continue;
                newClause.literals.emplace_back(lit);
            }
            for(auto lit:b.literals){
                if(!visited[lit] && lit!=literal && lit != complement(literal)){
                    newClause.literals.emplace_back(lit);  
                    visited[lit]=true;
                }                    
            }
            return newClause;
        }
        void printClause(){
            for(auto lit:literals){
                cout<<lit<<" ";
            }
            cout<<"##"<<endl;
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
            for(auto lit:cs.literals){
                #ifdef DEBUG3
                cout<<lit<<"@"<<state[lit].assigned<<" "<<state[complement(lit)].assigned<<endl;
                #endif
                if(state[lit].assigned==true)
                    return;
            }
            //cout<<endl;
            if(cs.isTautology())
                return;
            else{
                clauses.emplace_back(cs); // add to clauses
                if(cs.literals.size() == 1){ // It is a unit Clause
                    unitLiterals.emplace_back(cs.literals.front());
                    watchedLit.push_back({0,0});
                    //cout<<"unit here"<<endl;
                }
                else{
                    int flag=0,idx1,idx2=-1,lit1,lit2=-1;
                    for(int i=0;i<cs.literals.size();i++){
                        int k=cs.literals[i];                     
                        if(state[k].assigned == false && state[complement(k)].assigned==false){
                            if(flag)
                                {idx2=i;lit2=k;break;}
                            else
                                {idx1=i;lit1=k;flag=1;}
                        }
                    }
                    if(idx2==-1){
                        idx2=idx1,lit2=lit1;
                        // unitClause
                        unitLiterals.emplace_back(lit1);
                    }
                    #ifdef DEBUG3
                    cout<<idx1<<" "<<lit1<<" "<<idx2<<" "<<lit2<<endl;
                    cout<<clauses.size()<<" "<<cs.literals.size()<<endl;
                    #endif
                    watchedLit.push_back({idx1,idx2});
                    literalClauseMap[lit1]->insert(clauses.size()-1);
                    literalClauseMap[lit2]->insert(clauses.size()-1);
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
        bool isSatisfied(int clauseNum){
            for(auto lit:clauses[clauseNum].literals){
                if(state[lit].assigned)
                    return true;
            }
            return false;
        }
};
/**
 * SATsolver Class
 * Stores a pointer to clauseset object to access literalMap and all the clauses  
 */
int iter=0;
vector<clause>temporaryBuffer;
void unSet(vector<int>&unset){
    for(auto lit:unset){
        state[lit].assigned=false;
        depth[getvariable(lit)]=0;
        state[lit].antClause=0;
    }
}
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
        pair<bool,int> dpll(int satisfiedVariables,int level){ 

            /////////////UNIT PROPOGATION STARTS/////////////////
            vector <int> unset;
            // to keep track which unitLiterals are processed            
            vector <bool> visited(2*totalVariables+5);
            for(int i=0;i<unitLiterals.size();i++){

                int unitLiteral=unitLiterals[i];
                //cout<<unitLiteral<<"--"<<level<<endl;
                #ifdef DEBUG
                #endif
                if(visited[unitLiteral]) // if processed then continue;
                    continue;
                visited[unitLiteral]=true; // mark visited to true              
                if(state[complement(unitLiteral)].assigned){
                    #ifdef DEBUG
                    cout<<"fail state"<<" "<<unitLiteral<<" "<<level<<endl;
                    for(int i=1;i<=2*totalVariables;i++)
                        cout<<state[i].assigned<<" ";
                    cout<<endl;
                    for(auto lit:unset)
                        cout<<lit<<" ";
                    cout<<endl;
                    #endif
                    // clause addition
                    clause cl;
                    //cout<<unitLiteral<<" "<<state[unitLiteral].antClause<<"???"<<endl;
                    cl=clauseset->clauses[state[unitLiteral].antClause];
                    //cout<<state[unitLiteral].level<<"???????????????????????"<<level<<endl;
                    //cl.printClause();
                    for(int j=i-1;j>=0;j--){
                        int lit=unitLiterals[j];
                        if(state[lit].antClause==0)continue;
                        for(auto lit2:cl.literals){
                            if(lit2==lit || lit2==complement(lit)){
                                //cout<<lit<<"---";
                                //clauseset->clauses[state[lit].antClause].printClause();
                                cl=clause::resolution(cl,clauseset->clauses[state[lit].antClause],lit);
                                //cl.printClause();
                                int counter3=0,max1=0;
                                for(auto lit3:cl.literals){
                                    //cout<<state[lit3].level<<" "<<state[complement(lit3)].level<<endl;
                                    //assert(!(state[lit3].level!=0 && state[complement(lit3)].level!=0));
                                    int level1=depth[getvariable(lit3)];
                                    //cout<<lit3<<" "<<level<<" "<<level1<<endl;
                                    counter3+=(level1==level);
                                    if(level1!=level)
                                        max1=max(max1,level1);
                                }
                                //cout<<"??????????????????????"<<max1<<" "<<counter3<<endl;
                                if(max1==0)
                                    max1=level;
                                if(counter3==1){
                                    unitLiterals.clear();
                                    unSet(unset);
                                    cl.printClause();
                                    temporaryBuffer.emplace_back(cl);
                                    //cout<<level<<" jump to level "<<min(level-1,max1)<<endl;
                                    //cout<<level<<" "<<min(level-1,max1)<<endl;
                                    return {false,min(level-1,max1)};
                                }
                                //cl.printClause();
                            }
                        }
                    }
                    cl.printClause();                    
                    temporaryBuffer.push_back(cl); // go to the decision level and then add this clause
                    //clauseset->addClause(cl);
                    //assert(1==0); // should not reached here check again./
                    unitLiterals.clear();
                    unSet(unset);
                    return {false,level-1};
                }
                if(state[unitLiteral].assigned)continue;
                state[unitLiteral].assigned=true; // mark that literal set to true
                depth[(getvariable(unitLiteral))]=level;
                unset.emplace_back(unitLiteral);
                satisfiedVariables++;
                #ifdef DEBUG2
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
                        iter++;
                        if(clauseset->isSatisfied(clauseNum))continue;
                        int idx1=clauseset->watchedLit[clauseNum].first;
                        int idx2=clauseset->watchedLit[clauseNum].second;
                        bool flag=false;
                        if(clauseset->clauses[clauseNum].literals[idx1]==compUnitLiteral){
                            for(int i=0;i<clauseset->clauses[clauseNum].literals.size();i++){
                                if(i==idx2 || i==idx1)continue;
                                if(state[clauseset->clauses[clauseNum].literals[i]].assigned==false && 
                                    state[complement(clauseset->clauses[clauseNum].literals[i])].assigned==false)
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
                                //cout<<clauseNum<<"$$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx2]<<endl;
                                #endif
                                int newliteral=clauseset->clauses[clauseNum].literals[idx2];
                                unitLiterals.emplace_back(newliteral);
                                state[newliteral].antClause=clauseNum;
                                cout<<newliteral<<" "<<clauseNum<<"^^"<<endl;
                                // state[newliteral].level=level;
                            }
                        }else{
                             for(int i=0;i<clauseset->clauses[clauseNum].literals.size();i++){
                                if(i==idx2 || i==idx1)continue;
                               if(state[clauseset->clauses[clauseNum].literals[i]].assigned==false && 
                                    state[complement(clauseset->clauses[clauseNum].literals[i])].assigned==false)
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
                                //cout<<clauseNum<<"$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx1]<<endl;
                                #endif
                                int newliteral=clauseset->clauses[clauseNum].literals[idx1];
                                unitLiterals.emplace_back(newliteral);
                                state[newliteral].antClause=clauseNum;
                                cout<<newliteral<<" "<<clauseNum<<"^"<<endl;
                                // state[newliteral].level=level;
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
                    cout<<i<<"*"<<clauseset->watchedLit[i].first<<" "<<clauseset->watchedLit[i].second<<endl;;
                #endif
                // unSet(unset);
                return {true,0};
            }
            /////////////UNIT PROPOGATION COMPLETED/////////////////
            // clear the unitLiterals list as all of them been taken care of
               
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
           
            int random=rand()%2;
            // randomly choose either positive or negated literal
            // if(random%2==0)
            //     bestLiteral=complement(bestLiteral);

            ///////////// HEURISTIC ENDS ////////////////////////////

            // add the selected literal to unitLiterals
            
            /**
             * make a copy of current state and assigned vector   
             * all arguments are passed by refrence.
             * Doing this saves 1 copy. At each call only one copy is created
             * And this and the original are passed as refrences
             */

            // create a copy of current state
            //cout<<"?????????????????\n";
            // create a copy of assigned vector
            // 1st DPLL call
            while(1){
                int bestLiteral=0,bestValue=-1;
                for(int i=1;i<2*totalVariables;i+=2){
                    if(!state[i].assigned && !state[i+1].assigned){ // both the literals are unassigned
                        bestLiteral=i;
                        break;
                    }
                }
                if(bestLiteral==0){
                    unSet(unset);
                    return {false,level-1};
                }                
                unitLiterals.emplace_back(bestLiteral);
                pair<bool,int> ret=dpll(satisfiedVariables,level+1);
                cout<<ret.first<<" "<<ret.second<<"?"<<clauseset->clauses.size()<<endl;
                if(ret.first)
                    return {true,0};
                if(level>ret.second){ // this wants to go up more 
                    unSet(unset);
                    return {false,ret.second};
                }    
                else if(level==ret.second){
                    for(auto clause:temporaryBuffer)
                        clauseset->addClause(clause);
                    temporaryBuffer.clear();
                }
            }
            // unitLiterals.emplace_back(bestLiteral);
            // for(auto cl:temporaryBuffer)
            //     clauseset->addClause(cl);
            // temporaryBuffer.clear();          
            // remove the literal that was selected earlier and instead 
            // add the negation of that literal in unitLiterals
            // 2nd DPLL call
            //cout<<unitLiterals.size()<<endl;
            // unitLiterals.emplace_back(complement(bestLiteral));
            // pair<bool,int> ret2=dpll(satisfiedVariables,level+1);
            // if(ret2.first)
            //     return {true,0};
            // else
            // {
            //     unSet(unset);
            //     return {false,(int)min(level-1,ret2.second)};
            // }            
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
    state.resize(2*totalVariables+5);
    depth.resize(totalVariables+5);
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
    //cout<<"????????"<<endl;
    clause newc=clause::resolution(clauses.clauses[1],clauses.clauses[2],1); 
    //  for(int i=1;i<=2*totalVariables;i++)
    //     clauses.printLiteral(i);   
    SATsolver dpllsolver(&clauses); // solver object
    // assigned vector initially all false   

    // CALL TO SOLVER
    pair<bool,int> ret=dpllsolver.dpll(0,0); 
    cout<<ret.first<<endl;
    #ifdef OUTPUT
    if(!ret.first)
        cout<<"UNSAT\n";
    else{
        cout<<"SAT\n";
        for(int i=1;i<=totalVariables*2;i+=2){
            if(state[i].assigned)
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
            set|=state[lit].assigned;
        }
        assert(set==true);
    }   
    }
    #endif
    return 0; 
}