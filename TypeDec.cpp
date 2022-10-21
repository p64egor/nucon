#include "TypeDec.hpp"
#include "MyDefines.hpp"

std::string nameForPT(const ProveType pt)
{
    static std::string table [ctu32(ProveType::Empty)+1] =
    {
        "None",
        "Unspecified",
        "Axiom",
        "Program",
        "Empty"
    };

    return table[ctu32(pt)];
}


