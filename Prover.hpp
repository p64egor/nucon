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

#ifndef PROVER_HPP
#define PROVER_HPP

#include "TypeDec.hpp"
#include "Cond.hpp"

#include "MyDefines.hpp"

#include "Printer.hpp"

#include <vector>

extern bool g_bComputingCon;
extern bool g_bComputingNuCon;

class CProver;
extern CProver* g_prover;

const static std::string g_godelText = "This statement is not provable.";
const static std::string g_secondIncText = std::string("Con") + " -> " + g_godelText;




std::string negated_text(const std::string& str);
std::string opposite_of(const std::string& str);

std::vector<std::string> makeRefs(const std::string& strList);

bool implies(bool bL, bool bR);

bool modus_ponens_holds(bool bL, bool bR);

bool true_provable(bool bConclusion);

bool true_disprovable(bool bConclusion);

bool x_implies_true_implies_x(LockedFunc* pFunc);

bool true_truth(LockedFunc* pFunc);
bool false_truth(LockedFunc* pFunc);

bool propA(LockedFunc* pFunc);

bool propB(LockedFunc* pFunc);

bool propC(LockedFunc* pFunc);



struct Statement
{
    Statement();

    std::string Name;
    std::vector<Cond> Conds;

    std::string LHS;
    std::string RHS;

    bool Implication;

    bool Negated;

    bool Axiom;
};

bool detected_any_conds_have_self_ref(const Statement& statement);


struct ProvedStatement
{
    ProvedStatement();
    ProvedStatement(const std::string& strName);

    std::string Name;
    bool PT [ctu32(ProveType::Empty)];
};




bool induc_holds(const std::vector<uint8_t>& v);


bool statement_induc_holds(const Statement& statement);


bool statement_holds(const Statement& statement);
bool statement_provably_holds(const Statement& statement);

bool statement_circular(const Statement& statement, const ProveType pt = ProveType::Axiom);
bool statement_circular(const std::string& strFormula, const ProveType pt = ProveType::Axiom);

bool prover_consistent(LockedFunc* pFunc);

bool refcon(const Statement& statement);

bool ref_true(const Statement& statement);
bool direct_ref_not_true(const Statement& statement);
bool ref_false(const Statement& statement);
bool direct_ref_not_false(const Statement& statement);

void setup_misc_props();


class CProver
{
public:
    CProver();

    void add(const Statement& statement);

    std::vector<Statement>& statements();

    bool exists(const std::string& strStatement);

    bool statement_ref_statement(const std::string& strStatement, const std::string& strToFind);
    bool statement_ref_statement(const Statement& statement, const std::string& strToFind);

    bool statement_has_func(const std::string& strStatement, CondFunc func);

    Statement setup_statement(const std::string& strFormulaName, const std::vector<Cond>& conds, const bool bAxiom = false);
    Statement setup_statement(const std::string& strFormulaName, Cond cond, const bool bAxiom = false);

    Statement false_statement();
    Statement true_statement();
    Statement con_statement();

    bool consistent();

    bool known_as_circular(const std::string& strForumula);
    bool is_proving(const std::string& strFormula);
    bool proved(const std::string& strFormula, const ProveType pt);



protected:
    bool provable(const std::string& strStatement, const ProveType pt);
    bool not_provable(const std::string& strStatement, const ProveType pt);

    friend class LockedFunc;
    friend class CPrinter;
    friend bool prover_consistent(LockedFunc* pFunc);

private:
    std::vector<Statement> m_statements;

    std::vector<std::string> m_proving;
    std::vector<ProvedStatement> m_proved;

    std::vector<std::string> m_circular;

    void remove_from_proving(const std::string& strFormula);

    void clean_proving_cache_of(const std::string& strFormula);

    void add_as_proved(const std::string& strFormula, const ProveType pt);
    void add_as_circular(const std::string& strFormula);


    bool m_bInit;

    void setup();


};




bool prover_consistent(LockedFunc* pFunc);

#endif
