/*
nucon. nucon is a program that tries to prove is own consistency.
Copyright (C) 2022  p64egor
This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.
This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
*/

#include "Prover.hpp"

#include "MyDefines.hpp"
#include "Console.hpp"

#include "StringOps.hpp"

bool g_bComputingCon = false;


CProver* g_prover = nullptr;


Statement::Statement() : Name(""), LHS(""), RHS(""), Implication(false), Negated(false), Axiom(false)
{
}


bool detected_any_conds_have_self_ref(const Statement& statement)
{
    for (auto c : statement.Conds)
    {
        if (c.processed_self_ref_to_statement())
        {
            return true;
        }
    }

    return false;
}

ProvedStatement::ProvedStatement()
{
    for (uint32_t iii = 0; iii < ctu32(ProveType::Empty); ++iii)
    {
        PT[iii] = false;
    }
}

ProvedStatement::ProvedStatement(const std::string& strName)
{
    Name = strName;
    for (uint32_t iii = 0; iii < ctu32(ProveType::Empty); ++iii)
    {
        PT[iii] = false;
    }
}


std::string negated_text(const std::string& str)
{
    return std::string("!") + "(" + str + ")";
}


std::string opposite_of(const std::string& str)
{
    std::string strB;
    strB.append(str);

    if (strB.size() > 1)
    {
        bool bHasNeg = strB[0] == '!';
        bool bHasParen = strB[1] == '(';

        if (bHasNeg)
        {
            strB.erase(strB.begin());

            if (bHasParen)
            {
                strB.erase(strB.begin());
                strB.erase(strB.end() - 1);
            }

            return strB;
        }
        else
        {
            return negated_text(strB);
        }
    }

    return negated_text(strB);

}

std::vector<std::string> makeRefs(const std::string& strList)
{
    std::vector<std::string> frags = split(strList, ',');
    return frags;
}

bool implies(bool bL, bool bR)
{
    return !(bL && !bR);
}

bool modus_ponens_holds(bool bL, bool bR)
{
    return (bL && implies(bL, bR));
}

bool true_provable(bool bConclusion)
{
    return modus_ponens_holds(true, bConclusion);
}

bool true_disprovable(bool bConclusion)
{
    return modus_ponens_holds(true, !bConclusion);
}


bool x_implies_true_implies_x(LockedFunc* pFunc)
{
    const bool x = false;
    return implies(x, implies(true, x)) && implies(!x, implies(true, !x));
}




bool true_truth(LockedFunc* pFunc)
{
    return implies(true, true);
    //return (1 == 1);
}

bool false_truth(LockedFunc* pFunc)
{
    return implies(true, false);
    //return (0 == 1);
}



bool induc_holds(const std::vector<uint8_t>& v)
{
    if (v.size() == 0)
    {
        return false;
    }


    if (v[0])
    {
        for (uint32_t iii = 0; iii < v.size(); ++iii)
        {
            if (iii == v.size() - 1)
            {
                break;
            }

            if (!implies(v[iii], v[iii+1]))
            {
                return false;
            }
        }

        return true;
    }

    return false;
}


bool statement_induc_holds(const Statement& statement)
{
    std::vector<uint8_t> results;
    for (auto c : statement.Conds)
    {
        const bool b = c.Func();
        results.push_back(b);
    }

    const bool bIH = induc_holds(results);

    if (statement.Negated)
    {
        return true_disprovable(bIH);
    }

    return bIH;
}



CProver::CProver() : m_bInit(false)
{
    setup();
}

void CProver::add_to_lang(const Statement& statement)
{
    if (m_bInit)
    {
        // no adding allowed once initialized.
        return;
    }

    if (exists(statement.Name))
    {
        return;
    }


    const bool bImpliesScreening = true;
    if (bImpliesScreening)
    {
        if(statement.Implication)
        {
            if (!substr_exists(statement.LHS, g_provSym) && !substr_exists(statement.RHS, g_provSym))
            {
                if (!exists(statement.LHS) || !exists(statement.RHS))
                {
                    return;
                }
            }
        }
    }


    const bool bEnableAPIScreening = true;
    // prevent direct self-ref
    if (bEnableAPIScreening)
    {
        for (auto c : statement.Conds)
        {
            if (c.has_api_ref(statement.Name) || c.has_api_ref(opposite_of(statement.Name)))
            {
                return;
            }
        }


    }


    // when enabled, powerful way to catch self-refs.
    const bool bExistenceScreening = true;

    if (bExistenceScreening)
    {
        // do not allow conditions with api refs to sentences that do not yet exist.
        for (auto c : statement.Conds)
        {
            const std::vector<std::string>& ar = c.api_refs();
            for (uint32_t jjj = 0; jjj < ar.size(); ++jjj)
            {
                if (!exists(ar[jjj]))
                {
                    return;
                }
            }
        }
    }

    // don't allow two statemens to both directly ref the other.
    const bool bEnableAPIWebScreening = true;
    if (bEnableAPIWebScreening)
    {

        for (auto& s : m_statements)
        {
            if (s.Name == statement.Name)
            {
                continue;
            }

            bool b1 = false;
            bool b2 = false;

            for (auto c : s.Conds)
            {
                b1 = b1 || (c.has_api_ref(statement.Name) || c.has_api_ref(opposite_of(statement.Name)));
                if (b1)
                {
                    break;
                }
            }

            for (auto c : statement.Conds)
            {
                b2 = b2 || (c.has_api_ref(s.Name) || c.has_api_ref(opposite_of(s.Name)));
                if (b2)
                {
                    break;
                }
            }

            if (b1 && b2)
            {
                return;
            }

        }
    }



    m_statements.push_back(statement);

    if (statement.Axiom)
    {
        add_as_proved(statement.Name, ProveType::Unspecified);
    }

    const bool bEnsureNegWff = true;

    if (bEnsureNegWff)
    {
        if (!exists(opposite_of(statement.Name)))
        {
            Statement os;
            os = statement;
            os.Axiom = false;

            os.Negated = !statement.Negated;

            os.Name = opposite_of(statement.Name);

            m_statements.push_back(os);
        }
    }


}

std::vector<Statement>& CProver::statements()
{
    return m_statements;
}


bool CProver::exists(const std::string& strStatement)
{
    for (auto s : m_statements)
    {
        if (s.Name == strStatement)
        {
            return true;
        }
    }

    return false;
}


bool CProver::statement_ref_statement(const std::string& strStatement, const std::string& strToFind)
{
    Statement statement;
    bool bFound = false;
    for (auto s : m_statements)
    {
        if (s.Name == strStatement)
        {
            statement = s;
            bFound = true;
            break;
        }
    }

    if (!bFound)
    {
        return false;
    }

    return statement_ref_statement(statement, strToFind);
}

bool CProver::statement_ref_statement(const Statement& statement, const std::string& strToFind)
{
    if (statement.LHS == strToFind || statement.RHS == strToFind || statement.Name == strToFind)
    {
        return true;
    }

    if (statement_ref_statement(statement.LHS, strToFind) || statement_ref_statement(statement.RHS, strToFind))
    {
        return true;
    }

    return false;
}


bool CProver::statement_has_func(const std::string& strStatement, CondFunc func)
{
    for (auto s : m_statements)
    {
        if (s.Name == strStatement)
        {
            for (auto c : s.Conds)
            {
                if (c.has_cond_func(func))
                {
                    return true;
                }
            }

            break;
        }
    }

    return false;
}



Statement CProver::setup_statement(const std::string& strFormulaName, const std::vector<Cond>& conds, const bool bAxiom)
{
    Statement invalid;
    invalid.Name = "ERROR";

    if (!exists(strFormulaName))
    {

        Statement st;

        st.Name = strFormulaName;
        st.Axiom = bAxiom;

        for (auto c : conds)
        {
            st.Conds.push_back(c);
        }

        add_to_lang(st);

        return st;

    }

    for (auto s : m_statements)
    {
        if (s.Name == strFormulaName)
        {
            return s;
        }

    }

    return invalid;
}

Statement CProver::setup_statement(const std::string& strFormulaName, Cond cond, const bool bAxiom)
{

    std::vector<Cond> conds;
    conds.push_back(cond);

    return setup_statement(strFormulaName, conds, bAxiom);
}


Statement CProver::false_statement()
{
    Cond cond = Cond("False", false_truth);
    return setup_statement("False", cond);

}

Statement CProver::true_statement()
{
    Cond cond = Cond("True", true_truth);
    return setup_statement("True", cond);

}


Statement CProver::con_statement()
{
    Cond cond = Cond("Con", prover_consistent);
    return setup_statement("Con", cond);
}



void CProver::setup()
{
    m_bInit = false;

    g_prover = this;

    m_proving.clear();
    m_proved.clear();

    m_try_proved.clear();

    m_statements.clear();



    add_to_lang(false_statement());
    add_to_lang(true_statement());

    add_to_lang(con_statement());

    Statement fif;
    fif.Name = "False -> False";
    fif.LHS = "False";
    fif.RHS = "False";
    fif.Implication = true;
    g_prover->add_to_lang(fif);

    Statement tit;
    tit.Name = "True -> True";
    tit.LHS = "True";
    tit.RHS = "True";
    tit.Implication = true;
    g_prover->add_to_lang(tit);

    Statement fit;
    fit.Name = "False -> True";
    fit.LHS = "False";
    fit.RHS = "True";
    fit.Implication = true;
    g_prover->add_to_lang(fit);

    Cond condxtx = Cond("X -> (True -> X)", x_implies_true_implies_x);
    setup_statement("X -> (True -> X)", condxtx, true);

    setup_misc_props();

    std::vector<Statement> negated;
    for (auto s : m_statements)
    {
        if (!exists(opposite_of(s.Name)))
        {
            Statement ns = s;
            ns.Negated = !s.Negated;
            if (s.Axiom)
            {
                ns.Axiom = false;
            }

            ns.Name = opposite_of(s.Name);
            negated.push_back(ns);
        }

    }

    for (auto s : negated)
    {
        add_to_lang(s);
    }

    std::vector<Statement> negif;
    for (auto s : m_statements)
    {
        Statement ns = s;

        if (ns.Negated)
        {

            ns.Negated = !ns.Negated;

            ns.LHS = opposite_of(s.Name);
            ns.RHS = "False";

            ns.Name = "(" + ns.LHS + ")" + " -> " + ns.RHS;

            ns.Implication = true;
            ns.Conds.clear();
            negif.push_back(ns);
        }
    }

    for (auto s : negif)
    {
        add_to_lang(s);
    }

    std::vector<Statement> transps;
    for (auto s : m_statements)
    {
        Statement nis = s;
        if (nis.Implication && !nis.Negated)
        {
            nis.LHS = opposite_of(s.RHS);
            nis.RHS = opposite_of(s.LHS);

            nis.Name = nis.LHS + " -> " + nis.RHS;

            transps.push_back(nis);
        }
    }

    for (auto s : transps)
    {
        add_to_lang(s);
    }

    std::vector<Statement> fips;
    for (auto s : m_statements)
    {
        if (s.Name == "False" && !s.Negated)
        {
            continue;
        }

        Statement fis;
        fis.Name = std::string("False -> ") + "(" + s.Name + ")";

        fis.LHS = "False";
        fis.RHS = s.Name;
        fis.Implication = true;
        fips.push_back(fis);
    }


    for (auto s : fips)
    {
        add_to_lang(s);
    }





    m_bInit = true;

}


bool CProver::provable(const std::string& strStatement, const ProveType pt)
{

    if (strStatement.size() == 0)
    {
        return false;
    }

    if (strStatement[0] == g_provSym[0])
    {
        std::string strProvAlt = strStatement;
        strProvAlt.erase(strProvAlt.begin());

        return provable(strProvAlt, pt);
    }

    if (proved("False", ProveType::Unspecified) || proved(negated_text("True"), ProveType::Unspecified))
    {
        return true;
    }



    if (is_proving(strStatement) && m_proving.size() > 1)
    {
        if (m_proving[0] == strStatement)
        {
            add_as_circular(strStatement);
            return false;
        }
    }

    if (pt == ProveType::None || pt == ProveType::Empty)
    {
        return false;
    }


    if (proved(strStatement, ProveType::Unspecified))
    {
        return true;
    }



    for (auto s : m_statements)
    {
        if (s.Name == strStatement)
        {
            /*
                We must respect that if we proved two theories to which we
                can deduce strStatement, that we do so.
                Even if the strStatement is circular.
            */
            if (any_wff_implication_supports(s.Name))
            {
                add_as_proved(strStatement, ProveType::Unspecified);
                return true;
            }

        }
    }



    if (known_as_circular(strStatement))
    {
        return false;
    }

    if (strStatement == "True" || strStatement == negated_text("False"))
    {
        const bool b = true_provable(true);
        if (b)
        {
            add_as_proved(strStatement, ProveType::Unspecified);
            return true;
        }
    }


    if (is_proving(strStatement))
    {
        return false;
    }



    m_proving.push_back(strStatement);


    // ===================
    const bool bEnableProvInfer = true;
    if (bEnableProvInfer)
    {
        const bool bR0 = true;
        const bool bR1 = true;
        const bool bR2 = true;
        const bool bR3 = true;
        const bool bR4 = true;
        const bool bR5 = true;
        const bool bR6 = true;
        const bool bR7 = true;
        const bool bR8 = true;
        const bool bR9 = true;
        const bool bR10 = true;
        const bool bR11 = true;
        const bool bR12 = true;


        for (auto s : m_statements)
        {
            if (s.Name == strStatement)
            {
                if (s.Axiom)
                {
                    remove_from_proving(strStatement);
                    add_as_proved(strStatement, ProveType::Unspecified);
                    return true;
                }

                if (bR0)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (proved(s.LHS, ProveType::Unspecified) && proved(s.RHS, ProveType::Unspecified))
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }


                if (bR1)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.RHS == "True" || s.RHS == negated_text("False"))
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }


                if (bR2)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.LHS == s.RHS)
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }


                // implications involving consistency shall not be handled axiom-wise.
                // unless Con Or !Con has been proved.
                if (bR3)
                {
                    if (!(proved("Con", ProveType::Unspecified) || proved(negated_text("Con"), ProveType::Unspecified)))
                    {
                        if (s.Implication && !s.Negated)
                        {
                            if (refcon(s))
                            {
                                break;
                            }
                        }
                    }

                }



                if (bR4)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.RHS == "True -> True" || s.RHS == "False -> False")
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }


                if (bR5)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.LHS == "False" || s.LHS == negated_text("True"))
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }


                // if we proved the RHS, then we've proved X -> RHS
                if (bR6)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (proved(s.RHS, ProveType::Unspecified))
                        {
                            remove_from_proving(strStatement);
                            add_as_proved(strStatement, ProveType::Unspecified);
                            return true;
                        }
                    }
                }



                // if the opposite of the antecdent is provable..
                // ..then the antecedent implies false.
                if (bR7)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (opposite_of(s.LHS) != "False" && opposite_of(s.LHS) != negated_text("True"))
                        {
                            if (proved(opposite_of(s.LHS), ProveType::Unspecified) || try_provable(opposite_of(s.LHS), pt))
                            {
                                if (s.RHS == "False" || s.RHS == negated_text("True"))
                                {
                                    remove_from_proving(strStatement);
                                    add_as_proved(strStatement, pt);
                                    return true;
                                }
                            }
                        }

                    }
                }



                if (bR8)
                {
                    if (s.Implication && !s.Negated)
                    {

                        if (s.RHS == "False" || s.RHS == negated_text("True"))
                        {
                            if (is_proving("False") || is_proving(negated_text("True")))
                            {
                                remove_from_proving(strStatement);
                                return false;
                            }
                        }


                    }
                }


                if (bR9)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.RHS != "False" && s.RHS != negated_text("True"))
                        {
                            if (proved(s.RHS, ProveType::Unspecified) || try_provable(s.RHS, pt))
                            {
                                remove_from_proving(strStatement);
                                add_as_proved(strStatement, pt);
                                return true;
                            }
                        }

                    }
                }

                if (bR10)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.LHS == "True" && (is_proving(s.RHS) || is_proving(negated_text(s.RHS))))
                        {
                            remove_from_proving(strStatement);
                            return false;
                        }
                    }
                }



                if (bR11)
                {
                    for (auto s2 : m_statements)
                    {
                        if (!s2.Implication)
                        {
                            continue;
                        }

                        if (s2.Negated)
                        {
                            continue;
                        }

                        if (s2.LHS == "True" && is_proving(s2.RHS))
                        {
                            continue;
                        }

                        if (s2.LHS == "False" || s2.LHS == negated_text("True"))
                        {
                            continue;
                        }

                        if (s2.RHS == strStatement)
                        {
                            if (proved(s2.Name, ProveType::Unspecified) && provable(s2.LHS, ProveType::Unspecified))
                            {
                                remove_from_proving(strStatement);
                                add_as_proved(strStatement, pt);
                                return true;
                            }
                        }
                    }
                }


                if (bR12)
                {
                    if (s.Implication && !s.Negated)
                    {
                        if (s.RHS != "False" && s.RHS != negated_text("True"))
                        {
                            if (try_provable(s.LHS, pt) && try_provable(s.RHS, pt))
                            {
                                remove_from_proving(strStatement);
                                add_as_proved(strStatement, pt);
                                return true;
                            }
                        }
                    }
                }



                break;

            }
        }


    }


    // ===================


    // program utilizes different approach.
    if (pt != ProveType::Program && pt != ProveType::Unspecified)
    {
        remove_from_proving(strStatement);
        return false;
    }

    for (auto s : m_statements)
    {
        if (s.Name == strStatement)
        {
            // this loop does not handle implications
            if (s.Implication)
            {
                break;
            }

            if (strStatement == "False")
            {
                const bool sb1 = statement_provably_holds(s);
                const bool bCon = consistent();

                const bool sb2 = (sb1 || !bCon);


                remove_from_proving(strStatement);

                if (sb2)
                {
                    add_as_proved(strStatement, ProveType::Program);
                }

                return sb2;
            }
            else if (strStatement == negated_text("True"))
            {
                const bool sb1 = statement_provably_holds(s);
                const bool bCon = consistent();

                const bool sb2 = (sb1 || !bCon);


                remove_from_proving(strStatement);

                if (sb2)
                {
                    add_as_proved(strStatement, ProveType::Program);
                }

                return sb2;
            }


            const bool b = statement_provably_holds(s);

            remove_from_proving(strStatement);

            if (b)
            {
                add_as_proved(strStatement, ProveType::Program);
            }

            return b;
        }
    }

    remove_from_proving(strStatement);
    return false;
}


bool CProver::not_provable(const std::string& strStatement, const ProveType pt)
{
    return !provable(strStatement, pt);
}

bool CProver::try_provable(const std::string& strStatement, const ProveType pt)
{
    const bool bProv = provable(strStatement, pt);

    if (bProv)
    {
        if (!try_proved(strStatement))
        {
            // do something

            add_as_proved(g_provSym + strStatement, pt);


            m_try_proved.push_back(strStatement);
            m_try_proved.push_back(g_provSym + strStatement);

        }
    }

    return bProv;
}


bool CProver::try_not_provable(const std::string& strStatement, const ProveType pt)
{
    const bool bNotProv = try_not_provable(strStatement, pt);

    return bNotProv;
}

bool CProver::is_proving(const std::string& strFormula)
{
    for (auto s : m_proving)
    {
        if (s == strFormula)
        {
            return true;
        }
    }

    return false;
}

bool CProver::known_as_circular(const std::string& strFormula)
{
    for (auto s : m_circular)
    {
        if (s == strFormula)
        {
            return true;
        }
    }

    return false;
}

bool CProver::proved(const std::string& strFormula, const ProveType pt)
{
    const std::string& strFormulaAlt = g_provSym + strFormula;

    for (auto s : m_proved)
    {
        if (s.Name == strFormula || s.Name == strFormulaAlt)
        {
            if (s.PT[ctu32(ProveType::Unspecified)])
            {
                return true;
            }
            else if (pt == ProveType::Unspecified)
            {
                for (uint32_t iii = 0; iii < ctu32(ProveType::Empty); ++iii)
                {
                    if (s.PT[iii])
                    {
                        return true;
                    }
                }

                return false;
            }
            else if (s.PT[ctu32(pt)])
            {
                return true;
            }
        }

    }

    return false;
}

bool CProver::try_proved(const std::string& strFormula)
{
    for (auto s : m_try_proved)
    {
        if (s == strFormula)
        {
            return true;
        }
    }

    return false;
}

void CProver::remove_from_proving(const std::string& strFormula)
{
    const uint32_t nNegativeU32 = -1;

    uint32_t nIndex = nNegativeU32;

    for (uint32_t iii = 0; iii < m_proving.size(); ++iii)
    {
        if (m_proving[iii] == strFormula)
        {
            nIndex = iii;
            break;
        }
    }

    if (nIndex != nNegativeU32)
    {
        m_proving.erase(m_proving.begin() + nIndex);
    }

}

void CProver::clean_proving_cache_of(const std::string& strFormula)
{
    while (true)
    {

        uint32_t nIndex = NegativeUInt32;
        for (uint32_t iii = 0; iii < m_proving.size(); ++iii)
        {
            if (m_proving[iii] == strFormula)
            {
                nIndex = iii;
                break;
            }
        }

        if (nIndex != NegativeUInt32)
        {
            m_proving.erase(m_proving.begin() + nIndex);
        }
        else
        {
            break;
        }

    }
}

void CProver::add_as_proved(const std::string& strFormula, const ProveType pt)
{

    const bool bCleanUp = true;

    if (bCleanUp)
    {
        clean_proving_cache_of(strFormula);
    }

    for (auto s : m_proved)
    {
        if (s.Name == strFormula)
        {
            if (pt == ProveType::Unspecified)
            {
                for (uint32_t iii = 0; iii < ctu32(ProveType::Empty); ++iii)
                {
                    s.PT[iii] = true;
                }
            }
            else
            {

                s.PT[ctu32(pt)] = true;

            }

            return;
        }
    }


    ProvedStatement ps;
    ps.Name = strFormula;

    if (pt == ProveType::Unspecified)
    {
        for (uint32_t iii = 0; iii < ctu32(ProveType::Empty); ++iii)
        {
            ps.PT[iii] = true;
        }
    }
    else
    {

        ps.PT[ctu32(pt)] = true;

    }

    if (strFormula == g_godelText)
    {
        qp("Debug: Proved " + g_godelText);
    }

    if (strFormula == "Con")
    {
        qpc("Debug: Proved Con");
    }

    if (strFormula == g_secondIncText)
    {
        qpc("Debug: Proved Godel's Second Inc. Theorem.");
    }

    // for debugging
    if (strFormula == "False" || strFormula == negated_text("True"))
    {
        qpc("Warning: False was provable somehow!");
    }


    m_proved.push_back(ps);




}


void CProver::add_as_circular(const std::string& strFormula)
{
    for (auto s : m_circular)
    {
        if (s == strFormula)
        {
            return;
        }
    }

    m_circular.push_back(strFormula);
}


bool CProver::any_wff_implication_supports(const std::string& strFormula)
{

    for (auto s : m_statements)
    {
        if (s.Implication && !s.Negated)
        {
            if (s.RHS == strFormula)
            {
                if (proved(s.LHS, ProveType::Unspecified))
                {
                    if (proved(s.Name, ProveType::Unspecified) || proved(s.RHS, ProveType::Unspecified))
                    {
                        return true;
                    }

                }
            }

        }
    }

    return false;
}


bool CProver::consistent()
{
    const bool bResult = prover_consistent(nullptr);
    return bResult;
}




bool statement_holds(const Statement& statement)
{
    if (statement.Implication)
    {
        bool bL = false;
        bool bR = false;

        bool bGotL = false;
        bool bGotR = false;

        std::vector<Statement>& statements = g_prover->statements();

        for (uint32_t iii = 0; iii < statements.size(); ++iii)
        {
            if (!bGotL && statements[iii].Name == statement.LHS)
            {
                bL = statement_holds(statements[iii]);
                bGotL = true;

                if (!bL)
                {
                    // shortcut.
                    break;
                }
            }
            else if (!bGotR && statements[iii].Name == statement.RHS)
            {
                bR = statement_holds(statements[iii]);
                bGotR = true;

                if (bR)
                {
                    // shortcut.
                    break;
                }
            }

            if (bGotL && bGotR)
            {
                break;
            }
        }

        if (statement.Negated)
        {
            return implies(bL, bR);
        }
        else
        {
            return implies(bL, bR);
        }

    }

    bool bCondsHold = true;
    for (auto c : statement.Conds)
    {
        if (!c.Func())
        {
            bCondsHold = false;
            break;
        }
    }


    if (statement.Negated)
    {
        return !bCondsHold;
    }
    else
    {
        return bCondsHold;
    }


    return true;
}

bool statement_provably_holds(const Statement& statement)
{
    if (statement.Implication)
    {
        bool bL = false;
        bool bR = false;

        bool bGotL = false;
        bool bGotR = false;

        std::vector<Statement>& statements = g_prover->statements();

        for (uint32_t iii = 0; iii < statements.size(); ++iii)
        {
            if (!bGotL && statements[iii].Name == statement.LHS)
            {
                bL = statement_provably_holds(statements[iii]);
                bGotL = true;

                if (!bL)
                {
                    // shortcut.
                    break;
                }
            }
            else if (!bGotR && statements[iii].Name == statement.RHS)
            {
                bR = statement_provably_holds(statements[iii]);
                bGotR = true;

                if (bR)
                {
                    // shortcut.
                    break;
                }
            }

            if (bGotL && bGotR)
            {
                break;
            }
        }

        if (statement.Negated)
        {
            return true_disprovable(implies(bL, bR));
        }
        else
        {
            return true_provable(implies(bL, bR));
        }

    }

    const bool bInduc = statement_induc_holds(statement);



    if (detected_any_conds_have_self_ref(statement))
    {
        // Even if induction holds across the condition of a statement.
        // we do not say the statement is provableble if a self-ref was present.

        return false;
    }

    return bInduc;
}


bool refcon(const Statement& statement)
{
    if (statement.Implication)
    {
        if (statement.LHS == "Con" || statement.RHS == "Con")
        {
            return true;
        }
    }

    if (statement.Name == "Con")
    {
        return true;
    }

    for (auto c : statement.Conds)
    {
        if (c.has_cond_func(prover_consistent))
        {
            return true;
        }
    }

    return false;
}



bool ref_true(const Statement& statement)
{
    if (statement.Implication)
    {
        if (statement.LHS == "True" || statement.RHS == "True")
        {
            return true;
        }
    }

    // indirect reference of true
    if (direct_ref_not_false(statement))
    {
        return true;
    }


    for (auto c : statement.Conds)
    {
        if (c.has_cond_func(true_truth))
        {
            return true;
        }


    }

    return false;
}

bool direct_ref_not_true(const Statement& statement)
{
    const uint32_t nConds = statement.Conds.size();

    if (nConds == 1 && statement.Conds[0].has_cond_func(true_truth) && statement.Negated)
    {
        return true;
    }

    return false;
}

bool ref_false(const Statement& statement)
{
    if (statement.Implication)
    {
        if (statement.LHS == "False" || statement.RHS == "False")
        {
            return true;
        }
    }


    // indirect reference of false
    if (direct_ref_not_true(statement))
    {
        return true;
    }

    for (auto c : statement.Conds)
    {
        if (c.has_cond_func(false_truth))
        {
            return true;
        }

    }

    return false;
}

bool direct_ref_not_false(const Statement& statement)
{
    const uint32_t nConds = statement.Conds.size();

    if (nConds == 1 && statement.Conds[0].has_cond_func(false_truth) && statement.Negated)
    {
        return true;
    }

    return false;
}


bool propA(LockedFunc* pFunc)
{
    return (2 + 2 == 4);
}

bool propB(LockedFunc* pFunc)
{
    return (2 + 2 == 5);
}



bool propC(LockedFunc* pFunc)
{
    const uint32_t nAPIRefIndex = pFunc->indexForAPIRef(g_godelText);
    return !pFunc->probe_provable(nAPIRefIndex, ProveType::Program);
}




void setup_misc_props()
{
    //  add whatever custom props here.


    /*
    Uncomment to introduce contradiction:
    Statement ncon;
    ncon.Axiom = true;
    ncon.Name = "!(Con)";
    ncon.Conds.push_back(Cond("!(Con)", prover_consistent));
    ncon.Negated = true;
    g_prover->add(ncon);
    */

    Statement st2p2e4;
    st2p2e4.Name = "2p2e4";
    st2p2e4.Conds.push_back(Cond("2p2e4", propA));
    g_prover->add_to_lang(st2p2e4);


    Statement aiast2p2e4;
    aiast2p2e4.Name = "2p2e4 -> 2p2e4";
    aiast2p2e4.Implication = true;
    aiast2p2e4.LHS = "2p2e4";
    aiast2p2e4.RHS = "2p2e4";
    g_prover->add_to_lang(aiast2p2e4);


    Statement gfrd;
    gfrd.Name = "2p2e4 -> True";
    gfrd.Implication = true;
    gfrd.LHS = "2p2e4";
    gfrd.RHS = "True";
    g_prover->add_to_lang(gfrd);

    Statement st2p2e5;
    st2p2e5.Name = "2p2e5";
    st2p2e5.Conds.push_back(Cond("2p2e5",propB));
    g_prover->add_to_lang(st2p2e5);


    Statement g;
    g.Name = g_godelText;
    g.Conds.push_back(Cond(g_godelText, propC, makeRefs(g_godelText)));
    g_prover->add_to_lang(g);

    Statement gfact;
    gfact.Implication = true;
    gfact.LHS = g_provSym + g_godelText;
    gfact.RHS = opposite_of(g_godelText);
    gfact.Name = gfact.LHS + " -> " + gfact.RHS;

    // keep as axiom! ensures if we prove the godel sentence that we prove a contradiction.
    gfact.Axiom = true;

    g_prover->add_to_lang(gfact);


    Statement secit;
    secit.Name = g_secondIncText;
    secit.Implication = true;
    secit.LHS = "Con";
    secit.RHS = g_godelText;


    // may wish to uncomment for experiment.
    // secit.Axiom = true;


    g_prover->add_to_lang(secit);



}

bool prover_consistent(LockedFunc* pFunc)
{
    if (g_prover == nullptr)
    {
        return false;
    }



    if (g_bComputingCon)
    {
        qpc("Circular ref to Con detected.");


        return false;
    }

    g_bComputingCon = true;

    std::vector<Statement>& statements = g_prover->statements();

    for (auto s : statements)
    {

        if (g_prover->proved(s.Name, ProveType::Unspecified) && g_prover->proved(opposite_of(s.Name), ProveType::Unspecified))
        {
            g_bComputingCon = false;
            return false;
        }

        // these are important to keep
        if (refcon(s))
        {
            continue;
        }


        if (g_prover->statement_ref_statement(s.Name, "Con"))
        {
            continue;
        }

        if (g_prover->statement_ref_statement(s, negated_text("Con")))
        {
            continue;
        }

        if (s.Implication && !s.Negated)
        {
            if (s.LHS == "True" || s.LHS == negated_text("False"))
            {
                if (s.RHS == "False" || s.RHS == negated_text("True"))
                {
                    continue;
                }
            }

        }

        if (s.Implication && !s.Negated)
        {
            if ((s.LHS == "True" && s.RHS == "False") || (s.LHS == "True" && s.RHS == negated_text("True")))
            {
                continue;
            }

            if ((s.LHS == negated_text("False") && s.RHS == "False") || (s.LHS == negated_text("False") && s.RHS == negated_text("True")))
            {
                continue;
            }
        }



        if (s.Name == "False" || s.Name == negated_text("True"))
        {
            continue;
        }

        if (s.Name == "True" || s.Name == negated_text("False"))
        {
            continue;
        }


        if (true_provable(statement_holds(s)) && true_disprovable(statement_holds(s)))
        {
            g_bComputingCon = false;
            return false;
        }

        bool bP1 = false;
        bP1 = g_prover->try_provable(s.Name, ProveType::Program);

        bool bP2 = false;
        bP2 = g_prover->try_provable(opposite_of(s.Name), ProveType::Program);


        if (bP1 && bP2)
        {
            g_bComputingCon = false;
            return false;
        }



    }

    g_bComputingCon = false;

    return true;
}
