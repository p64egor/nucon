#ifndef PRINTER_HPP
#define PRINTER_HPP

#include "TypeDec.hpp"

#include <string>
#include <vector>

class CPrinter
{
public:
    CPrinter();

    void print_provability_of(const std::string& strFormulaName, const ProveType pt = ProveType::Axiom);
    void print_provability_tests(const ProveType pt, const std::vector<std::string>& formulas);



private:


};

#endif
