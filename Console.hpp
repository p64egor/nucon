#ifndef CONSOLE_HPP
#define CONSOLE_HPP

#include <vector>
#include <string>


#include <cstdint>


#include <vector>




// quick print
void qpc(const char* pText, const bool bEnd=true, const bool bAddToHistory=true);

// conditional quick print
bool cqpc(bool bCond, const char* pText, const bool bEnd=true, const bool bAddToHistory=true);


template <typename T>
void qp(const T& t, const bool bEnd=true, const bool bAddToHistory=true);

template <>
void qp(const bool& t, const bool bEnd, const bool bAddToHistory);

template <>
void qp(const std::string& t, const bool bEnd, const bool bAddToHistory);




// quick get input
std::string qgi(const bool bAddToHistory=true);

// quick add line input
void qalip(const std::string& strLine);

class CConsole;
class CConsole
{
public:
    CConsole();
    void init();
    void deInit();
    void frame(const float fFrameTime);
    void addLineInput(const std::string& strLine);
    void clearInputHistory();
    void addLineOutput(const std::string& strLine);
    void clearOutputHistory();
    void save(const std::string& strPath, const bool bIncludePrinted=false);
    std::vector<std::string> load(const std::string& strPath);
    void printLine(const std::string& strLine, const bool bEnd=true, const bool bAddToHistory=true);
    std::string getInput(const bool bAddToHistory=true);
private:
    std::vector<std::string> m_historyInput;
    std::vector<std::string> m_historyOutput;
    std::vector<std::string> m_loaded;
};

extern CConsole g_console;

#endif
