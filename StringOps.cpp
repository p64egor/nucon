#include "StringOps.hpp"
#include "MyDefines.hpp"

#include <sstream>


#include <ctime>

#include <boost/lexical_cast.hpp>



std::string getTimeStr()
{

    std::string strText;

    time_t rawTime;
    time(&rawTime);

    strText.append(ctime(&rawTime));

    return strText;
}

std::string strFromVecU8(const std::vector<uint8_t>& v, const bool bTrimAtNull)
{
    std::string str;


    if (bTrimAtNull)
    {
        for (uint32_t iii = 0; iii < v.size(); ++iii)
        {
            if (v[iii] == '\0')
            {
                break;
            }

            str.push_back(v[iii]);
        }
    }
    else
    {
        str.resize(v.size());

        for (uint32_t iii = 0; iii < v.size(); ++iii)
        {
            str[iii] = v[iii];
        }
    }

    return str;
}

std::vector<uint8_t> vecU8FromStr(const std::string& str, const bool bAddNull)
{
    std::vector<uint8_t> v;
    v.resize(str.size());

    for (uint32_t iii = 0; iii < str.size(); ++iii)
    {
        v[iii] = str[iii];
    }

    if (bAddNull)
    {
        v.push_back('\0');
    }

    return v;
}

std::string numstrFromVecU8(const std::vector<uint8_t>& v)
{
    std::string str;

    for (uint32_t iii = 0; iii < v.size(); ++iii)
    {
        str += ts((uint32_t)v[iii]);
    }

    return str;
}

void copyStrToArray(uint8_t* pArr, const std::string& str, const uint32_t nLimit)
{
    for (uint32_t iii = 0; iii < str.size(); ++iii)
    {
        if (iii >= nLimit)
        {
            break;
        }

        pArr[iii] = (uint8_t)str[iii];
    }
}

void copyVecU8ToArray(uint8_t* pArr, const std::vector<uint8_t>& v, const uint32_t nLimit)
{
    for (uint32_t iii = 0; iii < v.size(); ++iii)
    {
        if (iii >= nLimit)
        {
            break;
        }

        pArr[iii] = v[iii];
    }
}

template<typename Out>
void split(const std::string &s, char delim, Out result)
{
    std::stringstream ss(s);
    std::string item;
    while (std::getline(ss, item, delim))
    {
        *(result++) = item;
    }
}

std::vector<std::string> split(const std::string &s, char delim)
{
    std::vector<std::string> elems;
    split(s, delim, std::back_inserter(elems));
    return elems;
}

std::string split_and_get(const std::string &s, char delim, const uint32_t nIndex)
{
    std::vector<std::string> frags = split(s, delim);

    std::string str;

    if (frags.size() == 0)
    {
        return str;
    }

    if (nIndex >= frags.size())
    {
        return str;
    }

    str = frags[nIndex];

    return str;
}

template <typename T>
std::string ts(const T& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const bool& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}


template <>
std::string ts(const uint8_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const uint32_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const int32_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const int16_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const uint16_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const uint64_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const int64_t& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const float& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}

template <>
std::string ts(const double& t)
{
    std::stringstream ss;
    ss << t;
    return ss.str();
}



bool substr_exists(const std::string& strSrc, const std::string& strToFind)
{
    size_t nAt = strSrc.find(strToFind);
    return (nAt != std::string::npos);
}

