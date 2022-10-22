#ifndef TYPEDEC_HPP
#define TYPEDEC_HPP

#include <string>
#include <vector>


// function pointer for bool functions
typedef bool (*TruthFunc);

class LockedFunc;

typedef bool (*CondFunc)(LockedFunc* func);



enum class ProveType
{
    None,
    Unspecified,
    Axiom,
    Program,
    Empty
};

// keep as one symbol long!
const static std::string g_provSym = "*";

std::string nameForPT(const ProveType pt);


#endif
