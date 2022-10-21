#include "MyDefines.hpp"
#include "Console.hpp"

#include "Prover.hpp"


#include <assert.h>

using namespace std;

/*
    todos:
    -add plausible support for Provability in the statement symbolism.
    -resolve any remaining negation equivalence issues.
    -establish tests for well formedness somehow.
    -lockdown statements so the conds it has can't be called directly but by the Prover.
*/

void test();

int main()
{
    qpc("Program Started.");
	test();
	qpc("Program Over.");
	qgi();
	return 0;
}



void test()
{
	CProver prover;
	CPrinter printer;

	g_prover = &prover;

	qpc("=====Statements=====");
	std::vector<Statement> statements = prover.statements();

	for (auto s : statements)
	{
		qp(s.Name);
	}

	qpc("====================");

	qpc("");


	std::vector<std::string> forms;
	forms.push_back("True");
	forms.push_back("X -> (True -> X)");
	forms.push_back(negated_text("X -> (True -> X)"));
	forms.push_back("2p2e4");
	forms.push_back(negated_text("2p2e4"));

	forms.push_back("2p2e4 -> 2p2e4");
    forms.push_back(negated_text("2p2e4 -> 2p2e4"));

	forms.push_back("2p2e4 -> True");
    forms.push_back(negated_text("2p2e4 -> True"));

	forms.push_back("2p2e5");
	forms.push_back(negated_text("2p2e5"));

    forms.push_back(g_godelText);
    forms.push_back(negated_text(g_godelText));
    forms.push_back(negated_text("True"));

    forms.push_back("Con");
    forms.push_back(negated_text("Con"));

    forms.push_back("False");


    forms.push_back(g_secondIncText);
    forms.push_back(negated_text(g_secondIncText));



    qpc("===========================");
	printer.print_provability_tests(ProveType::Axiom, forms);
    qpc("===========================");
	printer.print_provability_tests(ProveType::Program, forms);
    qpc("===========================");
	printer.print_provability_tests(ProveType::Unspecified, forms);
    qpc("===========================");

	qpc("Test(s) finished.");


}
