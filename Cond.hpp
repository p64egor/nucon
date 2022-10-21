#ifndef COND_HPP
#define COND_HPP

#include "TypeDec.hpp"

#include <string>
#include <cstdint>

#include <vector>


class LockedFunc
{
    public:
    LockedFunc();
    LockedFunc(const std::string& strStatementOwner, CondFunc func);
    LockedFunc(const std::string& strStatementOwner, CondFunc func, const std::vector<std::string>& apiRefs);

    bool execute();

    bool try_provable(const uint32_t nAPIRefIndex, const ProveType pt);

    bool has_cond_func(CondFunc func) const;

    bool processed_self_ref_to_statement();

    uint32_t indexForAPIRef(const std::string& strRefToFind);

    private:
    std::string m_owner;
    std::vector<std::string> m_apiRefs;

    CondFunc m_func;
    bool m_executing;
    bool m_self_ref;

};



// important so we can check
struct Cond
{
public:

    Cond();
    Cond(const std::string& strOwner, CondFunc func);
    Cond(const std::string& strOwner, CondFunc func, const std::vector<std::string>& apiRefs);

    bool Func();

    bool has_cond_func(CondFunc func) const;

    bool processed_self_ref_to_statement();

    bool has_api_ref(const std::string& str) const;

private:
    std::string m_owner;
    LockedFunc m_lfunc;
    bool m_executing;
    std::vector<std::string> m_apiRefs;
};




#endif
