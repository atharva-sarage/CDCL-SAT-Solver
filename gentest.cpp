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
int main(int argc, char* argv[]) {
    srand(atoi(argv[1]));
	IOS;
    int n=rand(3,5);
    int m=rand(4,4);
    cout<<"p cnf "<<n<<" "<<m<<endl;
    while(m--){
        int lit1=rand()%2;
        if(lit1==0)
            lit1=-1;
        int lit2=rand()%2;
        if(lit2==0)
            lit2=-1;
        int lit3=rand()%2;
        if(lit3==0)
            lit3=-1;
        cout<<rand(1,n)*lit1<<" "<<rand(1,n)*lit2<<" "<<rand(1,n)*lit3<<" "<<0<<endl;
    }
	
	
}