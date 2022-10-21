#ifndef STRING_OPS_HPP
#define STRING_OPS_HPP

#include <cstdint>
#include <string>
#include <vector>

#include "MyDefines.hpp"


template<typename Out>
void split(const std::string &s, char delim, Out result);

std::vector<std::string> split(const std::string &s, char delim);
std::string split_and_get(const std::string &s, char delim, const uint32_t nIndex);

template <typename T>
std::string ts(const T& t);

template <>
std::string ts(const bool& t);

template <>
std::string ts(const uint8_t& t);

template <>
std::string ts(const uint32_t& t);

template <>
std::string ts(const int32_t& t);

template <>
std::string ts(const int16_t& t);

template <>
std::string ts(const uint16_t& t);

template <>
std::string ts(const uint64_t& t);

template <>
std::string ts(const int64_t& t);

template <>
std::string ts(const float& t);

template <>
std::string ts(const double& t);




bool substr_exists(const std::string& strSrc, const std::string& strToFind);



#endif
