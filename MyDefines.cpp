#include "MyDefines.hpp"


// to print out assert message
#include <iostream>


#include <bitset>

void qassert(const bool bCondition, const std::string& strText)
{
    if (!bCondition)
    {
        std::cout << "qassert: " << strText << std::endl;
        assert(bCondition);
    }
}

void fqassert(const std::string& strText)
{
    std::cout << "qassert: " << strText << std::endl;
    const bool bCondition = false;
    assert(bCondition);
}
