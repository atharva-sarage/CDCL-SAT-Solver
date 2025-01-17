/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
using namespace std;
// Global Variables
struct literalState{
    int assigned;  // value assigned to literal
    int level;     // the level of search tree at which this literal was assigned
    int antClause; // if it was an implied literal then it's antecedant clause
};
int conflicts;     // counter to denote Number of conflicts 
int threshold=100; // hyperparameter for restart after threshold many conflicts 
                   // we do a restart

/**
 * variableActivity stores a pair{activity,variable} for every variable,
 * Container is std::set. set is sorted in ascending order.
 * The highest activity variable is second entry corresponding to variableActivity's last pair.
 * We choose the highest activity variable for VSIDS
 */
// 
set<pair<int,int>>variableActivity; 
int satisfiedVariables=0; // counter for total number of satisfied variables
/**
 * level0Variables
 * all the literals which are true at level 0.
 * Literals are added to this when we learn a clause 
 * containing only one literal or unitsized clause was present in original clauses.
 * Forcing it to be true.
 */
vector<int>level0Literals;
vector<bool>finalAssignment;// stores the finalAssignment of the literals
/**
 * unitLiterals store the unitliteral which will be resolved during unitpropogation.
 * It is populated before the call to unitPropogation where it is used.Before returing
 * from unitPropogation it clears this vector.
 * If it is at level 0 then it is equal to level0Variables
 * If it is at any other level then it is equal decision taken at that level
 */
vector<int>unitLiterals;// stores the unitLiterals

vector <literalState> state;     // to store state of all literals
vector <int> depth;              // the level at which a variable was assigned
vector <int> decisionLiteral;    // the decision literal which was set to true at a given level
vector <int> currentScore;       // represents the current score of a given variable
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
        // Returns total Literals in a clause
        int getCountLiteralsInClause(){
            return totalLiterals;
        }
        // Returns whether clause is a tautology
        bool isTautology(){
            return tautology;
        }
        // returns the resoluted clause of 2 clauses  a ,b over a literal c
        // where one clause contains c and other contains negation c
        static clause resolution(clause a,clause b,int c){
            //visited- to keep track of which literals are added to resoluted clause
            // initiall set all to false
            vector<bool> visited(2*totalVariables+5,false);
            clause resolutedClause; // 
            for(auto lit:a.literals){
                visited[lit]=true;
                // if it is one of c or negation c do not add to new clause                
                if(lit==c || lit == complement(c)) 
                    continue;
                resolutedClause.literals.emplace_back(lit);
            }
            for(auto lit:b.literals){
                // if it is one of c or negation c do not add to new clause and not already added
                if(!visited[lit] && lit!=c && lit != complement(c)){
                    resolutedClause.literals.emplace_back(lit);  
                    visited[lit]=true;
                }                    
            }
            return resolutedClause;
        }
        // prints a clause
        void printClause(){
            for(auto lit:literals){
                cout<<lit<<" ";
            }
            cout<<endl;
        }
};
/**
 * Clause clauseSet
 * Stores all the clauses information
 */
class clauseSet{
    public:
        vector <clause> clauses; // vector of clause
        /**
         * Watched Literals Data Structures
         * literalClauseMap and watchedLit are the data structures used to implement 
         * 2 watched literals.
         * literalClauseMap:-
         * for each literal we keep a pointer to a list(container is unordered set) 
         * which stores, which clauses is this literal watching.
         * watchedLit:-
         * for each clause we keep 2 unassigned literals.
         * watchedLit[1] gives a pair, the 2 watched literals for clause 1
         */
        vector<unordered_set<int>*> literalClauseMap;  
        vector<pair<int,int>>watchedLit;    

        // state stores the initial state of all the clauses
        clauseSet(){                 
            // clauses are also 1 indexed put a dummy clause at 0 index
            clauses.emplace_back(clause(0));  
            watchedLit.push_back({-1,-1});
            // push the pointer of list(all clauses this literal is watching)
            // to the literalClauseMap                 
            for(int i=0;i<2*totalVariables+5;i++)
                literalClauseMap.push_back(new unordered_set<int>());           
        }
        /**
         * Add clause method add a clause to the clauseset only if it not
         * a tautology. It then updates countClause and the literalClauseMap
         */
        void addClause(clause cs){
            /**
             * Update the activity of variables
             * Initial activity is the occurance of that variable
             */
            for(auto lit:cs.literals){
                if(state[lit].assigned==true)
                    return;
                int var=getvariable(lit);
                assert(var!=0);
                // delete original pair and add inserted pair
                pair <int,int> deletePair={currentScore[var],var};
                currentScore[var]++; 
                pair <int,int> addPair={currentScore[var],var};
                variableActivity.erase(deletePair);
                variableActivity.insert(addPair);
            }
            
            if(cs.isTautology())
                return;
            else{
                clauses.emplace_back(cs); // add to clauses
                if(cs.literals.size() == 1){ // It is a unit sized Clause
                    level0Literals.emplace_back(cs.literals.front()); // add it to level0literals
                    /**
                     * assign level0Literals to unitLiterals which will be resolved while unitPropogation
                     * level0Literals are the literals that must be true. These are added when we learn                    
                     * a unit sized clause and backtrack to level 0. Now we set unitLiterals to level0Literals. 
                     * By a call to unitPropogation function all the inference is done at level 0.
                     */
                    unitLiterals=level0Literals; 
                    watchedLit.push_back({0,0}); // no need for watched literals                   
                }
                else{
                    /**
                     * We detect a unitClause if under current assignment we are
                     * able to find only 1 watched literal. If this happens then we 
                     * add this literal to unitLiterals as it must be set to true.
                     */
                    int flag=0,idx1,idx2=-1,lit1,lit2=-1,idx3,lit3;
                    for(int i=0;i<cs.literals.size();i++){
                        int k=cs.literals[i];      
                        // this is a unassigned literal               
                        if(state[k].assigned == false && state[complement(k)].assigned==false){
                            if(flag)
                                {idx2=i;lit2=k;break;} // 2nd unassigned literal and we break
                            else 
                                {idx1=i;lit1=k;flag=1;} // 1st unassigned
                        }
                        else{
                            idx3=i;lit3=k; // assigned literal
                        }
                    }
                    if(idx2==-1){ // we were not able to find 2nd watched literal
                        idx2=idx3,lit2=lit3; // se we set 2nd one arbritary
                        // unitClause
                        unitLiterals.emplace_back(lit1); // this clause must be unitClause so add it to unitLiterals
                    }
                    // update the watched literals data structure
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
        // function to check whether a clause is satisfied under current assignment
        bool isSatisfied(int clauseNum){
            for(auto lit:clauses[clauseNum].literals){
                if(state[lit].assigned)
                    return true;
            }
            return false;
        }
};
vector<clause>temporaryBuffer; // to store newly learned clause
/**
 * unSetInformation function unsets all literals provided as argument.
 * assigned to false,depth to 0,antclause to 0
 * also reduces satisfied variables counter
 */
void unSetInformation(vector<int>&unsetLiterals){
    for(auto lit:unsetLiterals){
        state[lit].assigned=false;
        depth[getvariable(lit)]=0;
        state[lit].antClause=0;
    }
    satisfiedVariables-=unsetLiterals.size();
}
/**
 * UnitPropogation Function
 * unitLiterals has all the literals that must be set to true 
 * unsetLiterals keeps track of all the literals that were set in this unitPropogation 
 * if we had to back track then we unset all the information that was
 * taken in this unitPropogation.
 * Returns {true,-1} No conflict and Formula is SAT
 *         {true,0 } No conflict but Formula is still not SAT
 *         {false,jumpLevel}  conflict was observed and we must backtrack to level jumplevel
 */
pair<bool,int>unitPropogation(vector<int>&unsetLiterals,int level,clauseSet* clauseset){

    // to keep track which unitLiterals are processed            
    vector <bool> visited(2*totalVariables+5);
    for(int i=0;i<unitLiterals.size();i++){
        int unitLiteral=unitLiterals[i];
        if(visited[unitLiteral]) // if processed then continue;
            continue;
        visited[unitLiteral]=true; // mark visited to true 
        /**
         * If complement of current unitLiteral is assigned
         * CONFLICT!!
         */
        if(state[complement(unitLiteral)].assigned){
            /**
             * Conflict at level 0 then formula is UNSAT. As level 0 forces all its 
             * variables to be true. return false.
             */
            if(level==0)
                return {false,-1};
            conflicts++;
            // VSIDS after a fixed num of conflicts(hyperparameter) activity of each variable
            // is halved
            if(conflicts%500==0){// divide activity by half
                auto itr=variableActivity.begin();
                while(itr!=variableActivity.end()){
                    auto itr2=itr;
                    itr++;
                    assert(itr2->second!=0);
                    pair<int,int>p1 = {1+itr2->first/2,itr2->second}; // 1 added as padding to avoid 0
                    variableActivity.erase(itr2);
                    variableActivity.insert(p1);
                    // update curretScore which stores score corresponding to each variable                    
                    currentScore[p1.second]=p1.first; 
                }
            }
                             
            // Learnt Clause Addition
            // cl is the antecedant clause of the unitLiteral involved in conflict
            /**
             * ALGORITHM:
             * We go in backward order for all the unitLiterals learned 
             * at the current level and resolve the current clause with 
             * the literal's antecedent clause. If we find UIP we stop 
             * and jump to the maximum level of just smaller than current level
             * and add this clause to the clause database.             * 
             */
            clause cl;
            cl=clauseset->clauses[state[unitLiteral].antClause];
            
            for(int j=i-1;j>=0;j--){
                int lit=unitLiterals[j];
                if(state[lit].antClause==0)continue;
                for(auto lit2:cl.literals){
                    if(lit2==lit || lit2==complement(lit)){ 
                        // this is the literal which on which we will resolve
                        cl=clause::resolution(cl,clauseset->clauses[state[lit].antClause],lit);
                        int counter3=0,max1=0;
                        for(auto lit3:cl.literals){
                            int level1=depth[getvariable(lit3)];
                            // count the number of variables which were assigned at current level
                            counter3+=(level1==level); 
                            if(level1!=level)
                                max1=max(max1,level1); // compute level just less than current level
                        }
                        // UIP obtained
                        if(counter3==1){
                            unitLiterals.clear();
                            // add this to temporary buffer. Role of temporary buffer is
                            // to store the clause temporarily and add it when we backtrack
                            // to level max1.
                            temporaryBuffer.emplace_back(cl);
                            return {false,max1};
                        }
                    }
                }
            }   
            // sholud not reach here
            assert(1==0);
        }

        if(state[unitLiteral].assigned)continue; // if already assigned continue
        // set the parameters
        state[unitLiteral].assigned=true; // mark that literal set to true
        depth[(getvariable(unitLiteral))]=level;
        unsetLiterals.emplace_back(unitLiteral);
        satisfiedVariables++;

        // Now we look at all the clauses where complement of this literal occurs   
        int compUnitLiteral=complement(unitLiteral);  

        vector <int> eraseList;
        if(clauseset->literalClauseMap[compUnitLiteral]->size()>0){  
            // iterate over all the clauses containing complement of that literal                       
            for(auto clauseNum:*(clauseset->literalClauseMap[compUnitLiteral])){                
                // if the clause is satisfied then move to next clause
                if(clauseset->isSatisfied(clauseNum))continue;
                // idx1 and idx2 are index corresponding to the watched literals in current clause
                int idx1=clauseset->watchedLit[clauseNum].first;
                int idx2=clauseset->watchedLit[clauseNum].second;
                bool flag=false;
                /**
                 * if it literal at index idx1 is compliteral it no more satisfies the invariant 
                 * that it should be unassigned and its complement must alas be unassigned
                 * so we need to find another one 
                 */
           
                if(clauseset->clauses[clauseNum].literals[idx1]==compUnitLiteral){
                    for(int i=0;i<clauseset->clauses[clauseNum].literals.size();i++){
                        if(i==idx2 || i==idx1)continue;
                        // pick an unassigned literal
                        if(state[clauseset->clauses[clauseNum].literals[i]].assigned==false && 
                            state[complement(clauseset->clauses[clauseNum].literals[i])].assigned==false)
                            {
                                // make updates to watched Literal data structures
                                clauseset->watchedLit[clauseNum].first=i;
                                clauseset->literalClauseMap[clauseset->clauses[clauseNum].literals[i]]->insert(clauseNum);
                                // now this clauseNum must be erased from list of of clauses watched by compliteral
                                // as it no longer watche it
                                eraseList.push_back(clauseNum);
                                flag=true;
                                break;
                            }
                    }
                    // we were not able to find an unassigned literals se the other watched literal for this clause
                    // must be true so we add it to unitLiterals
                    // and update the antecedent clause for this literal
                    if(!flag){
                        int newliteral=clauseset->clauses[clauseNum].literals[idx2];
                        unitLiterals.emplace_back(newliteral);
                        state[newliteral].antClause=clauseNum;
                    }
                } // same for the other watched literal
                else{
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
                        int newliteral=clauseset->clauses[clauseNum].literals[idx1];
                        unitLiterals.emplace_back(newliteral);
                        state[newliteral].antClause=clauseNum;
                    }
                }                     
            }  
            // delete all clauses that compUnitLiteral does not watch anymore
            for(auto k:eraseList){
                clauseset->literalClauseMap[compUnitLiteral]->erase(k);
            }
        }  
    }   
    // clear unitLiterals list as we have infered all possible information.
    unitLiterals.clear();
    if(satisfiedVariables==totalVariables) // WE ARE DONE -1 to denote this event
        return {true,-1};
    return {true,0}; // no conflict in unitPropogation go to deduce stage
}
/**
 * SATsolver Class
 * Stores a pointer to clauseset object to access literalMap and all the clauses  
 */
class SATsolver{
    private:        
        clauseSet* clauseset; // a pointer to clauseset object
    public: 
        SATsolver(clauseSet* cs):clauseset(cs){} // constructor which takes a pointer to clauseset
        /**
         * unitLiterals stores all the literals which are true at this level.
         * If it is level 0- then it is same as level0Variable(the varibles which are true at level 0)         
         * Else - it contains decion literal which was taken at this level.
         * 
         * Step1: unitLiterals vector has the all the unitLiterals which are true at level(argument of cdcl function).         * 
         * Step2: Do unitPropogation at this level if it return true then we are cool no conflict occured
         *         If it returned false then we cdcl returns false and backtracks to level set by unitpropogation
         * Step3: We pick a new variable that is not assigned till now and call cdcl(level+1)
         *        and call cdcl(level+1)
         *        now if it returns true we are done formula is SAT
         *        If it returns false and orderes to jump at lower level we unset all the information that
         *        was taken at this level and backtrack to appropriate level       
         *        It it tells us to stay at same level. Add new learned clause.
         *        Do unitpropogation with the same decision literal which was taken at this level to STEP 2         
         *
         * returns {true,0} if the formula is SAT
         *         {false,jumpLevel} conflict was observed and we jump to jumpLevel
         */
        pair<bool,int> cdcl(int level){ 
            vector <int> unsetLiterals;
            pair<bool,int>retVal=unitPropogation(unsetLiterals,level,clauseset);
            /**
             * If there is a conflict then retVal's first element is false.
             * If we are at level 0 and there is a conflict during unitPropogation
             * then the formula is UNSAT. And we are done!!
             * If we are not at level 0 we jump to state which unitPropagation ordered us.
             * The level is the second element of pair
             * If retVal returs true we go to decide stage where we pick new variable 
             */            
            if(retVal.first!=true){
                // unSet all the variables which were set during call to unitPropogation.
                // there should no side effect due to unitPropogation if there was conflict.
                unSetInformation(unsetLiterals);  
                unsetLiterals.clear();              
                return retVal;
            }
            if(retVal.second == -1){
                return {true,0};
            }
            // clear unitLiterals as we infered all the information by literals
            // in this list so we clear it.
            unitLiterals.clear();
            int temp=0;
            vector<int>unsetLiterals2;

            while(1){
                
                //Choose the variable with highest activity which is still unassigned.                
                int bestLiteral=0,bestValue=-1;              
                for(auto it=variableActivity.rbegin();it!=variableActivity.rend();++it){
                    int var=it->second;                       
                    if(!state[2*var].assigned && !state[2*var-1].assigned){ // both the literals are unassigned
                        bestLiteral=2*var-1;
                        break;
                    }
                }         
                /**
                 * RESTART 
                 * after conflicts cross threshold we do a restart.
                 * Also update threshold after every restart
                 * Reusing the Assignment Trail in CDCL Solvers 
                 * http://satassociation.org/jsat/index.php/jsat/article/view/89
                 * partial restart to Reduced Trail (as per paper terminology)
                 * We have some decision trail and now we do a restart
                 * New decision variables will be chosen according to Current activity of variables
                 * Let x next be the unassigned variable with the highest activity – 
                 * in other words the next decision variable if no restart would be performed. 
                 * The key insight is that any assignment that is made before x next after
                 * a restart must also have been assigned before the restart.
                 *  The ReusedTrail level (RTL) is the highest level up to which
                 *  all decision variables score higher than x next in the VSIDS order.
                 *  This means that each of these would be part of the trail after a full restart.
                 *  This gives performance some performance improvement
                 */
                 
                int nextVariableActivivty=currentScore[getvariable(bestLiteral)];
                if(conflicts==threshold){
                    // restart
                    int restartLevel;                   
                   
                    for(int i=1;i<=level;i++){
                        restartLevel=i;
                        if(currentScore[getvariable(decisionLiteral[level])]<nextVariableActivivty)
                            break;
                    }
                 
                    // clear all the unitLiterals list and 
                    // unitPropogation infromation( more details on line 576)
                    // as we jumping to new level.
                    unSetInformation(unsetLiterals); 
                    unSetInformation(unsetLiterals2); 
                    unsetLiterals.clear();
                    unsetLiterals2.clear();
                    unitLiterals.clear();
                    threshold=threshold*2; // increase threshold to delay next restart
                    return {false,restartLevel-1};
                }           
                
                int random=rand()%2;
                // // randomly choose either positive or negated literal
                if(random%2==0)
                    bestLiteral=complement(bestLiteral);   
                // add the decision variable in the begining to unitLiteral list as this must be set to true
                // unitPropogation will handle it.       
                unitLiterals.insert(unitLiterals.begin(),bestLiteral);
                /**
                 * Imagine we are at middle point of the edge that connects level d 
                 * to level d+1. At this point we decide what should be the next decision 
                 * variable. So this new variable we pick is decision variable for level d+1.
                 * NOTE: decision for level d has already been taken and we need to take
                 * decision for d+1.
                 * unitLiterals will hold this decision variable.
                 * Which is true(since it is a unitLiteral and inference will be done
                 * while unitPropogation function in cdcl function )
                 */
                decisionLiteral[level+1]=bestLiteral;
                // make a call to cdcl 
                pair<bool,int> ret=cdcl(level+1);

                if(ret.first) // we are done
                    return {true,0};
                // we either go up or stay at same level so 
                // discard current decision variable taken at this level(best literal)
                decisionLiteral[level+1]=0; 
                /**
                 * Discard unitpropogation information:
                 * It is stored in either
                 * unsetLiterals(first unitPropogation at this level)
                 * unsetLiterals2(any other unitPropogation at this level)
                 * it may happen that we learn clause at keep comming back to same 
                 * level. When this happens for the first time unsetLiterals has the
                 * information any subsequent unitpropogation information is 
                 * present in unsetLiterals2.          *
                 * So we need to clear this information so we call unsetInformation 
                 */
                unSetInformation(unsetLiterals); 
                unSetInformation(unsetLiterals2); 
                unsetLiterals.clear();
                unsetLiterals2.clear();
                //  wants to go up the decision level as per returned value
                if(level>ret.second){                      
                    return {false,ret.second};
                }    
                else if(level==ret.second){ // jumped back to same level
                    // add the learned clause which was stored in temporaryBuffer
                    for(auto clause:temporaryBuffer)
                        clauseset->addClause(clause); 
                    temporaryBuffer.clear();
                    /**
                     * first we deduce as we have learned a new clause do unitPropogation
                     * if are not at level 0 we again start unitpropogation with the
                     * decision literal which was taken at current level
                     * If we are at level 0 we should do unitPropogation with all 
                     * the unitSized literals which are stored in level0literals
                     */
                    if(level!=0) 
                        unitLiterals.emplace_back(decisionLiteral[level]); 
                    else
                        unitLiterals=level0Literals;
                    // do unitPropogation at current level
                    pair<bool,int> retVal2=unitPropogation(unsetLiterals2,level,clauseset);
                    // if returend false conflict occured and we go up the tree
                    // as returned by unitPropogation
                    if(retVal2.first==false){
                        unSetInformation(unsetLiterals2);
                        unsetLiterals2.clear();
                        return retVal2;
                    }
                    // returned value was true and -1 is second element means
                    // satisfiedvariable == totalvariables
                    // so formula is sat we return true
                    if(retVal2.second==-1){                  
                      return {true,0};
                    }
                    // no conflict was observed in unitPropogation
                }
            }          
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
    // resize vectors to save time
    state.resize(2*totalVariables+5);
    depth.resize(totalVariables+5);
    decisionLiteral.resize(totalVariables+5);
    currentScore.resize(totalVariables+5);
    clauseSet clauses; // clauseset object
    vector<int>input; // stores literals
    for(int i=1;i<=totalVariables;i++)
        variableActivity.insert({0,i});
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

    SATsolver cdclsolver(&clauses); // solver object
    // CALL TO SOLVER
    pair<bool,int> ret=cdclsolver.cdcl(0);    
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
        // for(auto k:clauses.clauses){
        // bool set=false;
        // for(auto lit: k.literals){
        //     if(lit==0)
        //         {set=true;break;}                         
        //     set|=state[lit].assigned;
        // }
        // assert(set==true);
        //}   
    }
    return 0; 
}
