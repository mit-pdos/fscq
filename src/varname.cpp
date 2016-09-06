#include <iostream>

using namespace std;

int main()
{
    int limit;
    
	cout << "please enter element number: ";
	cin >> limit;	
	cout << endl;
    cout << endl;
    cout << endl;

	for(int count = 3; count <= limit; count++)
{
	if (count % 2 == 0)
	{
    cout << "Theorem destruct_varname" << count << " : forall ";
    for (int i = 1; i <= count; i++)
        cout << "XN" << i << " " << "X" << i << " ";
    cout << "X" << count+1 << " ";
    cout << endl << "\t\t\t\t" << "(p : ";
    for (int i = 1; i <= count; i++)
        if (i != count)
            cout << "(XN" << i << " * X" << i << ") * (";
        else
            cout << "(XN" << i << " * X" << i << ") * X" << i+1;
    for (int i = 0; i < count; i++)
        cout << ")";
    cout <<",\n\texists ";
    for (int i = 1; i <= count; i++)
        cout << "xn" << i << " " << "x" << i << " ";
    cout << "x" << count+1;
    cout << ", p = (";
    for (int i = 1; i <= count; i++)
        if (i != count)
            cout << "(xn" << i << ", x" << i << "), (";
        else
            cout << "(xn" << i << ", x" << i << "), x" << i+1;
    for (int i = 0; i < count; i++)
        cout << ")";
    cout << ".\n";
    cout << "Proof. intros. repeat destruct_prod. repeat eexists. Qed." << endl;
	
	cout << endl;
	
	cout << "Ltac destruct_varname" << count << " :=" << endl;
    cout << "\t" << "match goal with" << endl;
    cout << "\t" << "| [ H : ";
    for (int i = 0; i < count; i++)
        if (i != count - 1)
            cout << "VARNAME (_) * _ * (";
        else
            cout << "(VARNAME (_) * _) * _";
    for (int i = 1; i < count; i++)
        cout << ")";
    cout << " |- _ ] =>" << endl;
    cout << "\t" << "\t" << "let Hx := fresh in" << endl;
    cout << "\t" << "\t" << "pose proof (destruct_varname" << count << " H) as Hx;" << endl;
    cout << "\t" << "\t" << "match type of Hx with" << endl;
    cout << "\t" << "\t" << "| exists ";
    for (int i = 0; i < count; i++)
        cout << "(_ : VARNAME (vn" << i+1 << ")) _ ";
    cout << "_ , _ = _ =>" << endl;
    cout << "\t" << "\t" << "\t" << "destruct Hx as ";
    for (int i = 0; i < count; i++)
        cout << "[? [?vn" << i+1 << " ";
    cout << "[? Hx]";
    for (int i = 0; i < count; i++)
        cout << " ] ]";
    cout << endl;
    cout << "\t" << "\t" << "end" << endl;
    cout << "\t" << "end." << endl;
    cout << endl;
    }
}
	
        cout << "Ltac destruct_varnames :=" << endl;
    cout << "\t" << "repeat (( ";
    for (int i = limit; i > 0; i--)
    	if (i % 2 == 0)
            cout << "destruct_varname" << i << " || ";

     cout << "destruct_varname1); subst)." << endl;
    cout << endl;
    cout << endl;
    return 0;
}

