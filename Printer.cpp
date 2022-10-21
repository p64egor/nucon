#include "Printer.hpp"

#include "Console.hpp"

#include "Prover.hpp"


CPrinter::CPrinter()
{
}



void CPrinter::print_provability_of(const std::string& strFormulaName, const ProveType pt)
{
    qp("Attempting to asses provability of " + strFormulaName);

    // pre-establish what program can prove on its own first.


    const std::string strPTName = nameForPT(pt);


    const bool bProved = g_prover->provable(strFormulaName, pt);

    if (bProved)
    {
        qp(strFormulaName + " is " + strPTName +" provable.");
    }
    else
    {
        qp(strFormulaName + " is NOT " + strPTName + " provable.");
    }

    qpc("");
}


void CPrinter::print_provability_tests(const ProveType pt, const std::vector<std::string>& formulas)
{
    // pre-cycle through what's provable.

    const bool bPreCycle = true;
    if (bPreCycle)
    {
        uint32_t nCalls = 0;
        uint32_t nProved = 0;
        const uint32_t nCallsExpected = formulas.size() * 2;

        for (auto s : formulas)
        {
            const bool bProved = g_prover->provable(s, ProveType::Program);
            if (bProved)
            {
                nProved += 1;
            }
            nCalls += 1;
        }

        for (auto s : formulas)
        {
            const bool bProved = g_prover->provable(s, ProveType::Program);
            if (bProved)
            {
                nProved += 1;
            }
            nCalls += 1;
        }

        if (nCalls != nCallsExpected || nProved == 0)
        {
            qpc("Error with Pre-Cycle.");
            return;
        }
    }


    qpc("");
    for (auto s : formulas)
    {
        print_provability_of(s, pt);
    }
    qpc("");
}

