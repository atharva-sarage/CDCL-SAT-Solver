/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
using namespace std;
//#define DEBUG
//#define DEBUG3
//#define LEARNEDCLAUSES
//#define OUTPUT
// Global Variables for storing finalAssignment and totalNumberofClauses and Variables
struct variableState{
    int assigned,level,antClause;
};
int conflicts;
int threshold=100;
set<pair<int,int>>variableActivity;
vector<int>level0Variables;
vector<bool>finalAssignment;
vector<int>unitLiterals;
vector <variableState> state;
vector <int> depth;
vector <int> decisionLiteral;
vector <int> currentScore;
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
            vector<bool> visited(2*totalVariables+5,false);
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
            // cout<<"resolution start"<<" "<<literal<<endl;
            // a.printClause();
            // b.printClause();
            // newClause.printClause();
            // cout<<"resolution done"<<endl;
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
            //cout<<clauses.size()<<endl;
            // cs.printClause();
            for(auto lit:cs.literals){
                if(state[lit].assigned==true)
                    return;
                int var=getvariable(lit);
                assert(var!=0);
                pair <int,int> deletePair={currentScore[var],var};
                currentScore[var]++; 
                pair <int,int> addPair={currentScore[var],var};
                variableActivity.erase(deletePair);
                variableActivity.insert(addPair);
            }

            //cout<<endl;
            if(cs.isTautology())
                return;
            else{
                clauses.emplace_back(cs); // add to clauses
                if(cs.literals.size() == 1){ // It is a unit Clause
                    level0Variables.emplace_back(cs.literals.front());
                    unitLiterals=level0Variables;
                    watchedLit.push_back({0,0});
                    #ifdef DEBUG
                    //cout<<"unit here "<<cs.literals.front()<<endl;
                    cout<<"Learned unit clause"<<" "<<cs.literals.front()<<endl;
                    #endif
                }
                else{
                    int flag=0,idx1,idx2=-1,lit1,lit2=-1,idx3,lit3;
                    for(int i=0;i<cs.literals.size();i++){
                        int k=cs.literals[i];                     
                        if(state[k].assigned == false && state[complement(k)].assigned==false){
                            if(flag)
                                {idx2=i;lit2=k;break;}
                            else
                                {idx1=i;lit1=k;flag=1;}
                        }
                        else{
                            idx3=i;lit3=k;
                        }
                    }
                    if(idx2==-1){
                        idx2=idx3,lit2=lit3;
                        // unitClause
                        #ifdef DEBUG
                        cout<<"unit here"<<endl;
                        #endif
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
int satisfiedVariables=0;
void unSet(vector<int>&unset,int flag=1){
    for(auto lit:unset){
        state[lit].assigned=false;
        depth[getvariable(lit)]=0;
        state[lit].antClause=0;
    }
    if(flag)
        satisfiedVariables-=unset.size();
}
pair<bool,int>unitPropogation(vector<int>&unset,int level,clauseSet* clauseset){

    // to keep track which unitLiterals are processed            
    vector <bool> visited(2*totalVariables+5);
    for(int i=0;i<unitLiterals.size();i++){
        int unitLiteral=unitLiterals[i];
        #ifdef DEBUG
        #endif
        if(visited[unitLiteral]) // if processed then continue;
            continue;
        visited[unitLiteral]=true; // mark visited to true 
        //cout<<unitLiteral<<"--"<<level<<" "<<state[unitLiteral].antClause<<endl;
        // if(level==0){
        //     cout<<"level 0\n";
        //     clauseset->clauses[state[unitLiteral].antClause].printClause();
        //     //1416
        // }            
        #ifdef DEBUG             
        #endif
        if(state[complement(unitLiteral)].assigned){
            conflicts++;
            if(conflicts%500==0){// divide activity by half
                auto itr=variableActivity.begin();
                while(itr!=variableActivity.end()){
                    auto itr2=itr;
                    itr++;
                    assert(itr2->second!=0);
                    pair<int,int>p1 = {1+itr2->first/2,itr2->second};
                    variableActivity.erase(itr2);
                    variableActivity.insert(p1);
                    currentScore[p1.second]=p1.first;
                }
                // if(conflicts==threshold){
                //     // restart
                //     unitLiterals.clear();
                //     threshold=threshold*1.5;
                //     return {false,0};
                // }                            
            }
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
            #ifdef DEBUG
            #endif
            for(int j=i-1;j>=0;j--){
                int lit=unitLiterals[j];
                if(state[lit].antClause==0)continue;
                for(auto lit2:cl.literals){
                    if(lit2==lit || lit2==complement(lit)){
                        #ifdef DEBUG
                        cout<<lit<<"---"<<endl;
                        clauseset->clauses[state[lit].antClause].printClause();
                        #endif
                        cl=clause::resolution(cl,clauseset->clauses[state[lit].antClause],lit);
                        #ifdef DEBUG
                        cl.printClause();
                        #endif
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
                        // if(max1==0) // if only one variable at current level go to level 0
                        //     max1=level;
                        if(counter3==1){
                            unitLiterals.clear();
                            temporaryBuffer.emplace_back(cl);
                            //cout<<level<<" jump to level "<<min(level-1,max1)<<endl;
                            #ifdef LEARNEDCLAUSES
                            cl.printClause();
                            //cout<<level<<" "<<max1<<"====="<<min(level-1,max1)<<endl;
                            #endif
                            return {false,max1};
                        }
                        //cl.printClause();
                    }
                }
            }
            #ifdef LEARNEDCLAUSES
            cl.printClause();                    
            for(int i=1;i<=level;i++)
                cout<<i<<" "<<decisionLiteral[i]<<endl;
            cout<<"no uip"<<endl;
            #endif
            if(cl.literals.size()!=1){
                // cout<<level<<endl;
                //assert(1==0); // check again
            }
            temporaryBuffer.push_back(cl); // go to the decision level and then add this clause
            //clauseset->addClause(cl);
            //assert(1==0); // should not reached here check again./
            unitLiterals.clear();            
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
        #ifdef DEBUG
        cout<<compUnitLiteral<<"$$$$$$$"<<clauseset->literalClauseMap[compUnitLiteral]->size()<<endl;
        #endif
        vector <int> eraseList;
        if(clauseset->literalClauseMap[compUnitLiteral]->size()>0){  
            // iterate over all the clauses containing complement of that literal                       
            for(auto clauseNum:*(clauseset->literalClauseMap[compUnitLiteral])){
                iter++;
                // cout<<clauseNum<<"$#$#$#$#"<<endl;
                // for(int i=1;i<=2*totalVariables;i++){
                //     cout<<state[i].assigned<<" ";
                // }
                // cout<<endl;
                if(clauseset->isSatisfied(clauseNum))continue;
                #ifdef DEBUG
                #endif
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
                        cout<<clauseNum<<"$$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx2]<<endl;
                        #endif
                        int newliteral=clauseset->clauses[clauseNum].literals[idx2];
                        unitLiterals.emplace_back(newliteral);
                        state[newliteral].antClause=clauseNum;
                        //cout<<newliteral<<" "<<clauseNum<<"^^"<<endl;
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
                        cout<<clauseNum<<"$$"<<compUnitLiteral<<" "<<clauseset->clauses[clauseNum].literals[idx1]<<endl;
                        #endif
                        int newliteral=clauseset->clauses[clauseNum].literals[idx1];
                        unitLiterals.emplace_back(newliteral);
                        state[newliteral].antClause=clauseNum;
                        //cout<<newliteral<<" "<<clauseNum<<"^"<<endl;
                        // state[newliteral].level=level;
                    }
                }                     
            }  
            for(auto k:eraseList){
                clauseset->literalClauseMap[compUnitLiteral]->erase(k);
            }
        }  
    }   
    unitLiterals.clear();
    #ifdef DEBUG
    cout<<satisfiedVariables<<endl;
    #endif
    int satisfiedVariables2=0;
    for(int i=1;i<=2*totalVariables;i++)
        satisfiedVariables2+=state[i].assigned;
    assert(satisfiedVariables2==satisfiedVariables);
    if(satisfiedVariables==totalVariables)
        return {true,-1};
    return {true,0}; // no conflict in unitPropogation go to deduce stage
}
class SATsolver{
    private:        
        clauseSet* clauseset; // a pointer to clauseset object
    public: 
        SATsolver(clauseSet* cs):clauseset(cs){} // constructor which takes a pointer to clauseset
        pair<bool,int> cdcl(int level){ 
            //cout<<level<<endl;
            vector <int> unset;
            /////////////UNIT PROPOGATION STARTS/////////////////
            pair<bool,int>retVal=unitPropogation(unset,level,clauseset);
            if(retVal.first!=true){
                unSet(unset);  
                unset.clear();              
                return retVal;
            }
            // int satisfiedVariables2=0;
            // for(int i=1;i<=2*totalVariables;i++)
            //     satisfiedVariables2+=state[i].assigned;
            //assert(satisfiedVariables==satisfiedVariables2);
            if(satisfiedVariables==totalVariables){
                return {true,0};
            }
            unitLiterals.clear();
            int temp=0;
            vector<int>unset2;

            while(1){
                int bestLiteral=0,bestValue=-1;              
                for(auto it=variableActivity.rbegin();it!=variableActivity.rend();++it){
                    int var=it->second;                       
                    if(!state[2*var].assigned && !state[2*var-1].assigned){ // both the literals are unassigned
                        bestLiteral=2*var-1;
                        break;
                    }
                }              
                // cout<<"????"<<getvariable(bestLiteral)<<endl;
                // for(int i=1;i<2*totalVariables;i+=2){
                //     if(!state[i].assigned && !state[i+1].assigned){ // both the literals are unassigned
                //         bestLiteral=i;
                //         break;
                //     }
                // }
                if(bestLiteral==0){
                    unSet(unset);
                    assert("1==0"); // analyse this case
                    return {false,level-1};
                }      
                int random=rand()%2;
                // randomly choose either positive or negated literal
                if(random%2==0)
                    bestLiteral=complement(bestLiteral);          
                unitLiterals.insert(unitLiterals.begin(),bestLiteral);
                decisionLiteral[level+1]=bestLiteral;
                //cout<<satisfiedVariables<<"satisfied variables"<<endl;
                pair<bool,int> ret=cdcl(level+1);
                #ifdef DEBUG
                #endif
                if(ret.first)
                    return {true,0};
                decisionLiteral[level+1]=0; // we either go up or stay at same level so 
                // discard current decision variable taken at this level(best literal)
                unSet(unset); // check again as we need to restart even if same level
                unSet(unset2); // throw previous unit propogation information
                unset.clear();
                unset2.clear();
                if(level>ret.second){ // this wants to go up more                     
                    return {false,ret.second};
                }    
                else if(level==ret.second){
                    for(auto clause:temporaryBuffer)
                        clauseset->addClause(clause);
                    temporaryBuffer.clear();
                    #ifdef DEBUG
                    cout<<decisionLiteral[level]<<" decision literal"<<endl;   
                    for(int i=1;i<=2*totalVariables;i++)
                        cout<<state[i].assigned<<" ";
                    cout<<endl;
                    #endif
                    if(level!=0) // check again
                        unitLiterals.emplace_back(decisionLiteral[level]);
                    else
                        unitLiterals=level0Variables;
                    pair<bool,int> retVal2=unitPropogation(unset2,level,clauseset);
                    #ifdef DEBUG
                    for(auto k:unset2)
                        cout<<k<<"::::";
                    cout<<"????"<<endl;
                    cout<<"done deduce"<<" "<<retVal2.first<<endl;
                    for(int i=1;i<=2*totalVariables;i++)
                        cout<<state[i].assigned<<" ";
                    cout<<endl;
                    #endif
                    //assert(retVal2.first==true);// check again if unit literal clause
                    // is returned then false;
                    //cout<<satisfiedVariables<<" "<<totalVariables<<endl;                    
                    if(retVal2.first==false){
                        unSet(unset2);
                        unset2.clear();
                        return retVal2;
                    }
                    if(retVal2.second==-1){                  
                      return {true,0};
                    }
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
    //cout<<"????????"<<endl;
    //  for(int i=1;i<=2*totalVariables;i++)
    //     clauses.printLiteral(i);   
    SATsolver cdclsolver(&clauses); // solver object
    // assigned vector initially all false   

    // CALL TO SOLVER
    pair<bool,int> ret=cdclsolver.cdcl(0); 
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