#include "Console.hpp"


#include "StringOps.hpp"

#include <iterator>

#include <fstream>

#include <iostream>

#include <sstream>
using namespace std;



CConsole g_console;

void qpc(const char* pText, const bool bEnd, const bool bAddToHistory)
{
    std::string strText;
    strText.append(pText);

    g_console.printLine(strText, bEnd, bAddToHistory);
}

// conditional quick print
bool cqpc(bool bCond, const char* pText, const bool bEnd, const bool bAddToHistory)
{
    if (bCond)
    {
        qpc(pText, bEnd, bAddToHistory);
    }

    return bCond;
}

template <typename T>
void qp(const T& t, const bool bEnd, const bool bAddToHistory)
{
    std::string strText;
    strText = ts(t);
    g_console.printLine(strText, bEnd, bAddToHistory);
}

template <>
void qp(const bool& t, const bool bEnd, const bool bAddToHistory)
{
    std::string strText;
    strText = ts(t);
    g_console.printLine(strText, bEnd, bAddToHistory);
}

template <>
void qp(const std::string& t, const bool bEnd, const bool bAddToHistory)
{
    std::string strText;
    strText = t;
    g_console.printLine(strText, bEnd, bAddToHistory);
}

std::string qgi(const bool bAddToHistory)
{
    return g_console.getInput(bAddToHistory);
}

void qalip(const std::string& strLine)
{
    g_console.addLineInput(strLine);
}

CConsole::CConsole()
{

}

void CConsole::init()
{

    m_historyInput.clear();
    m_historyOutput.clear();
}

void CConsole::deInit()
{
    m_historyInput.clear();
    m_historyOutput.clear();
}

void CConsole::frame(const float fFrameTime)
{

}

void CConsole::addLineInput(const std::string& strLine)
{
    m_historyInput.push_back(strLine);
}

void CConsole::clearInputHistory()
{
    m_historyInput.clear();
}

void CConsole::addLineOutput(const std::string& strLine)
{
    m_historyOutput.push_back(strLine);
}

void CConsole::clearOutputHistory()
{
    m_historyOutput.clear();
}

void CConsole::save(const std::string& strPath, const bool bIncludePrinted)
{
    std::ofstream ofs (strPath.c_str(), std::ofstream::binary);

    ofs << "[Outputs]" << endl;

    if (!ofs)
    {
        printLine("failed to open file. @console save", true, false);
        return;
    }

    if (bIncludePrinted)
    {
        for (uint32_t iii = 0; iii < m_historyOutput.size(); ++iii)
        {
            ofs << m_historyOutput[iii] << endl;
        }
    }

    ofs << "[Inputs]" << endl;

    for (uint32_t iii = 0; iii < m_historyInput.size(); ++iii)
    {
        ofs << m_historyInput[iii] << endl;
    }

    ofs.close();
}

std::vector<std::string> CConsole::load(const std::string& strPath)
{


    std::vector<std::string> content;
    std::ifstream ifs(strPath.c_str(), std::ifstream::binary);

    if (!ifs)
    {
        printLine("failed to open file. @console load", true, false);
        return content;
    }

    if (m_loaded.size() > 0)
    {
        m_loaded.clear();
    }

    std::string strInput;
    while (ifs)
    {

        uint8_t nChar = 0;
        ifs.read((char*)&nChar, sizeof(uint8_t));

        if (nChar != 10)
        {
            strInput.push_back(nChar);
        }


        if (nChar == 10)
        {
            content.push_back(strInput);
            strInput.clear();
            continue;
        }

    }

    ifs.close();

    m_loaded = content;

    return content;

}

void CConsole::printLine(const std::string& strLine, const bool bEnd, const bool bAddToHistory)
{
    if (bAddToHistory)
    {
        m_historyOutput.push_back(strLine);
    }

    cout << strLine;
    if (bEnd)
    {
        cout << '\n';
    }
}

std::string CConsole::getInput(const bool bAddToHistory)
{
    std::string strText;
    getline(cin, strText);

    if (bAddToHistory)
    {
        m_historyInput.push_back(strText);
    }


    return strText;
}
