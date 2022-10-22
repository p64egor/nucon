#include "Cond.hpp"

#include "Prover.hpp"

#include "Console.hpp"

#include "StringOps.hpp"

LockedFunc::LockedFunc()
{
    m_owner = "";
    m_func = nullptr;
    m_executing = false;
    m_apiRefs = std::vector<std::string>();
    m_self_ref = false;
}


LockedFunc::LockedFunc(const std::string& strStatementOwner, CondFunc func)
{
    m_owner = strStatementOwner;
    m_func = func;
    m_executing = false;
    m_apiRefs = std::vector<std::string>();
    m_self_ref = false;
}


LockedFunc::LockedFunc(const std::string& strStatementOwner, CondFunc func, const std::vector<std::string>& apiRefs)
{
    m_owner = strStatementOwner;
    m_func = func;
    m_executing = false;
    m_apiRefs = apiRefs;
    m_self_ref = false;
}


bool LockedFunc::execute()
{
    if (m_func == nullptr)
    {
        qp("LockedFunc for" + m_owner + " lacks truth cond.");
        return false;
    }

    if (m_executing)
    {
        qp("LockedFunc for" + m_owner + " was caught looping.");
        return false;
    }

    m_executing = true;

    const bool b = m_func(this);

    m_executing = false;

    return b;
}

bool LockedFunc::try_provable(const uint32_t nAPIRefIndex, const ProveType pt)
{
    std::string strStatement = "";
    if (nAPIRefIndex >= m_apiRefs.size())
    {
        return false;
    }

    strStatement = m_apiRefs[nAPIRefIndex];

    if (substr_exists(strStatement, g_provSym) || substr_exists(strStatement, opposite_of(g_provSym)))
    {
        return false;
    }

    // can pre-catch a circular loop.
    if (strStatement == m_owner || strStatement == opposite_of(m_owner))
    {
        m_self_ref = true;
        return false;
    }

    if (substr_exists(strStatement, m_owner) || substr_exists(strStatement, opposite_of(m_owner)))
    {
        m_self_ref = true;
        return false;
    }


    if (!g_prover->statement_has_func(strStatement, m_func))
    {
        return false;
    }

    return g_prover->try_provable(strStatement, pt);
}



bool LockedFunc::has_cond_func(CondFunc func) const
{
    return (m_func == func);
}

bool LockedFunc::processed_self_ref_to_statement()
{
    return m_self_ref;
}

uint32_t LockedFunc::indexForAPIRef(const std::string& strRefToFind)
{
    for (uint32_t iii = 0; iii < m_apiRefs.size(); ++iii)
    {
        if (m_apiRefs[iii] == strRefToFind)
        {
            return iii;
        }
    }

    return NegativeUInt32;
}


Cond::Cond()
{
    m_owner = "";
    m_executing = false;
    m_apiRefs = std::vector<std::string>();

}

Cond::Cond(const std::string& strOwner, CondFunc func)
{
    m_owner = strOwner;
    m_apiRefs = std::vector<std::string>();

    m_lfunc = LockedFunc(strOwner, func, m_apiRefs);
    m_executing = false;

}


Cond::Cond(const std::string& strOwner, CondFunc func, const std::vector<std::string>& apiRefs)
{
    m_owner = strOwner;
    m_apiRefs = apiRefs;

    m_lfunc = LockedFunc(strOwner, func, apiRefs);
    m_executing = false;


}

bool Cond::Func()
{
    if (m_executing)
    {
        qp("Cond for" + m_owner + " was caught looping.");
        return false;
    }

    m_executing = true;

    const bool b = m_lfunc.execute();

    m_executing = false;

    return b;
}

bool Cond::has_cond_func(CondFunc func) const
{
    return m_lfunc.has_cond_func(func);
}

bool Cond::processed_self_ref_to_statement()
{
    return m_lfunc.processed_self_ref_to_statement();
}

bool Cond::has_api_ref(const std::string& str) const
{
    for (auto s: m_apiRefs)
    {
        if (s == str)
        {
            return true;
        }
    }

    return false;
}

const std::vector<std::string>& Cond::api_refs()
{
    return m_apiRefs;
}
