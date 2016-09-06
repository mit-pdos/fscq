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
	if (count % 2 == 0) {
    cout << "Theorem destruct_pair" << count << " : forall ";
    for (int i = 0; i < count; i++)
        cout << "X" << i + 1 << " ";
    cout << "(p : ";
    for (int i = 0; i < count; i++)
        if (i != count -1)
            cout << "X" << i+1 << " * ";
        else
            cout << "X" << i+1 << ")," << endl;
    cout << "\t" << "exists ";
    for (int i = 0; i < count; i++)
        cout << "x" << i +1 << " ";
    cout << ", p = (";
    for (int i = 0; i < count; i++)
        if (i != count -1)
            cout << "x" << i+1 << ", ";
        else
            cout << "x" << i+1 << ")." << endl;
    cout << "Proof. intros; do " << count - 1 <<" destruct p; repeat eexists. Qed." << endl;
    
    cout << endl;
    
    cout << "Ltac destruct_pair" << count << " :=" << endl;
    cout << "\t" << "match goal with" << endl;
    cout << "\t" << "| [ H : ";
    for (int i = 1; i < count; i++)
        cout << "_ * ";
    cout << "_|- _ ] => first [ clear H ||  let Hx := fresh in" << endl;
    cout << "\t" << "\t" << "pose proof (destruct_pair" << count <<" H) as Hx;" << endl;
    cout << "\t" << "\t" << "match type of Hx with" << endl;
    cout << "\t" << "\t" << "| exists ";
    for (int i = 0; i < count; i++)
        cout << "_ ";
    cout << ", _ = _ =>" << endl;
    cout << "\t" << "\t" << "destruct Hx as ";
    for (int i = 0; i < count; i++)
        cout << "[? ";
    cout << "Hx";
    for (int i = 0; i < count; i++)
        cout << " ]";
   cout << endl;
   cout << "\t" << "\t" << "end ]" << endl;
   cout << "\t" << "end." << endl;
	
	cout << endl;
	}
}
	
    cout << "Ltac destruct_pair_once :=" << endl;
    cout << "\t" << "match goal with" << endl;
	cout << "\t" << "| [ v: valuset |- _ ] =>" << endl;
	cout << "\t" << "  let v0 := fresh v \"_cur\" in" << endl;
	cout << "\t" << "  let v1 := fresh v \"_old\" in" << endl;
	cout << "\t" << "  destruct v as [v0 v1]" << endl;
	

	cout << "\t" << "| _ => ( " << endl;
	for (int i = limit; i > 1; i--)
		if (i % 2 == 0)
        if (i != 2)
            cout << "destruct_pair" << i << " || ";
        else
            cout << "destruct_pair" << i << ")" << endl;
	cout << "\t" << "end; subst." << endl;
    cout << endl;
    cout << endl;
    return 0;
}


/*
Ltac destruct_pair_once :=
  match goal with
  | [ v: valuset |- _ ] =>
    let v0 := fresh v "_cur" in
    let v1 := fresh v "_old" in
    destruct v as [v0 v1]
  | _ => ( destruct_pair16 || destruct_pair14 || destruct_pair12 || destruct_pair10 || destruct_pair8 || destruct_pair6 || destruct_pair4 || destruct_pair2)
  end; subst.
*/
