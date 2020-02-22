/******************************************
*    AUTHOR:         Atharva Sarage       *
*    INSTITUITION:   IIT HYDERABAD        *
******************************************/
#include<bits/stdc++.h>
#warning Check Max_Limit,Overflows
using namespace std;
# define IOS ios::sync_with_stdio(0);cin.tie(0);cout.tie(0);
# define ff first
# define ss second
# define pb push_back
# define mod 1000000007
# define ll long long 
# define db double
# define inf 1e9
# define mx2 100005
# define mx 100005
int rand(int a, int b) {
    return a + rand() % (b - a + 1);
}
// 5,10 30 60
// 
int main(int argc, char* argv[]) {
    srand(atoi(argv[1]));
	IOS;
    int n=rand(5,10);
    int m=rand(30,60);
    cout<<"p cnf "<<n<<" "<<m<<endl;
    while(m--){      
        set<int>s;
        while(s.size()<3){
            int lit1=rand()%2;
            if(lit1==0)lit1=-1;
            int num=rand(1,n);
            s.insert(num*lit1);
        }
        for(auto k:s)
            cout<<k<<" ";
        cout<<0<<endl;
    }
	
	
}
// 8 15
/*
p cnf 4 12
-3 -1 2 0
-4 -2 3 0
-4 -2 4 0
-4 -3 2 0
-4 -3 1 0
-2 -1 4 0
1 3 4 0
1 2 4 0
-4 -2 -1 0
-4 1 3 0
-3 1 4 0
-1 1 4 0
*/
/*
p cnf 4 10
-3 1 2 0
-4 1 3 0
-2 1 2 0
-2 3 4 0
1 2 4 0
-4 2 3 0
-3 -2 -1 0
-4 -3 1 0
-3 1 4 0
-4 -2 3 0
*/