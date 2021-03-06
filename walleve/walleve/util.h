// Copyright (c) 2016-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef  WALLEVE_UTIL_H
#define  WALLEVE_UTIL_H

#include "walleve/type.h"
#include <boost/date_time.hpp>
#include <boost/asio/ip/address.hpp>

#if defined __linux__
#include <net/if.h>
#include <ifaddrs.h>
#include <netpacket/packet.h>
#elif defined __APPLE__
#include <ifaddrs.h>
#include <net/if.h>
#include <net/if_types.h>
#include <net/if_dl.h>
#endif

namespace walleve
{


extern bool STD_DEBUG;
extern const uint64 SUPERNODE_INNER_NONCE;

inline int64 GetTime()
{
using namespace boost::posix_time;
    static ptime epoch(boost::gregorian::date(1970, 1, 1));
    return int64((second_clock::universal_time() - epoch).total_seconds());
}

inline int64 GetTimeMillis()
{
using namespace boost::posix_time;
    static ptime epoch(boost::gregorian::date(1970, 1, 1));
    return int64((microsec_clock::universal_time() - epoch).total_milliseconds());
}

inline std::string GetLocalTime()
{
using namespace boost::posix_time;
    time_facet *facet = new time_facet("%Y-%m-%d %H:%M:%S");
    std::stringstream ss;
    ss.imbue(std::locale(std::locale("C"), facet));
    ss << second_clock::universal_time();
    return ss.str();
}

class CTicks
{
public:
    CTicks() : t(boost::posix_time::microsec_clock::universal_time()) {}
    int64 operator- (const CTicks& ticks) const { return ((t - ticks.t).ticks()); }
    int64 Elapse() const { return ((boost::posix_time::microsec_clock::universal_time() - t).ticks()); } 
public:
    boost::posix_time::ptime t;
};

inline void StdDebug(const char* pszName, const char* pszErr)
{
    if (STD_DEBUG)
    {
        std::cout << GetLocalTime() << " [DEBUG] <" << pszName << "> " << pszErr << std::endl;
    }
}

inline void StdLog(const char* pszName, const char* pszErr)
{
    std::cout << GetLocalTime() << " [INFO] <" << pszName << "> " << pszErr << std::endl;
}

inline void StdWarn(const char* pszName, const char* pszErr)
{
    std::cerr << GetLocalTime() << " [WARN] <" << pszName << "> " << pszErr << std::endl;
}

inline void StdError(const char* pszName, const char* pszErr)
{
    std::cerr << GetLocalTime() << " [ERROR] <" << pszName << "> " << pszErr << std::endl;
}

// Get An interface's mac addr
inline bool GetAnIFMacAddress(std::vector<uint8>& vecMac)
{
    bool success = false;
#if (defined __linux__) || (defined __APPLE__)
    struct ifaddrs *ifaddr=NULL;
    struct ifaddrs *ifa = NULL;
    int i = 0;

    std::vector<std::vector<uint8>> vecMacList;
    if (getifaddrs(&ifaddr) == -1)
    {
        return success;
    }

    for ( ifa = ifaddr; ifa != NULL; ifa = ifa->ifa_next)
    {
        std::vector<uint8> data;
#if defined __linux__
        if (ifa->ifa_addr && ifa->ifa_addr->sa_family == AF_PACKET && !(ifa->ifa_flags & IFF_LOOPBACK))
        {
            struct sockaddr_ll *s = (struct sockaddr_ll*)ifa->ifa_addr;
            std::copy_n(&(s->sll_addr[0]), s->sll_halen, std::back_inserter(data));
            vecMacList.push_back(data);
        }
#else
        if (ifa->ifa_addr && ifa->ifa_addr->sa_family == AF_LINK && !(ifa->ifa_flags & IFF_LOOPBACK))
        {
            struct sockaddr_dl * sdl = (struct sockaddr_dl *) ifa->ifa_addr;
            if (sdl->sdl_type == IFT_ETHER)
            {
                std::copy_n((uint8*)sdl->sdl_data + sdl->sdl_nlen, sdl->sdl_alen, std::back_inserter(data));
            }
        }
#endif
        if (!data.empty())
        {
            vecMacList.push_back(data);
        }
    }
    freeifaddrs(ifaddr);
    
    success = vecMacList.size() > 0 ? true : false;
    if (success) 
    {
        std::sort(vecMacList.begin(), vecMacList.end());
        vecMac = std::move(vecMacList.front());
    }
#endif
    return success;
}

inline bool IsRoutable(const boost::asio::ip::address& address)
{
    if (address.is_loopback() || address.is_unspecified())
    {
        return false;
    }
    if (address.is_v4())
    {        
        unsigned long u = address.to_v4().to_ulong();
        
        // RFC1918 https://tools.ietf.org/html/rfc1918
        // IP address space for private internets
        // 0x0A000000 => 10.0.0.0 prefix
        // 0xC0A80000 => 192.168.0.0 prefix
        // 0x0xAC100000 - 0xAC200000 => 172.16.0.0 - 172.31.0.0 prefix
        if ((u & 0xFF000000) == 0x0A000000 || (u & 0xFFFF0000) == 0xC0A80000 
            || (u >= 0xAC100000 && u < 0xAC200000))
        {
            return false;
        }
        
        // RFC3927 https://tools.ietf.org/html/rfc3927
        // IPv4 Link-Local addresses
        // 0xA9FE0000 => 169.254.0.0 prefix
        if ((u & 0xFFFF0000) == 0xA9FE0000)
        {
            return false;
        }
    }
    else
    {
        boost::asio::ip::address_v6::bytes_type b = address.to_v6().to_bytes();
        
        // RFC4862 https://tools.ietf.org/html/rfc4862
        // IPv6 Link-local addresses
        // FE80::/64
        if (b[0] == 0xFE && b[1] == 0x80 && b[2] == 0 && b[3] == 0 
            && b[4] == 0 && b[5] == 0 && b[6] == 0 && b[7] == 0)
        {
            return false;
        }
        
        // RFC4193 https://tools.ietf.org/html/rfc4193
        // Local IPv6 Unicast Addresses
        // FC00::/7 prefix
        if ((b[0] & 0xFE) == 0xFC)
        {
            return false;
        }
        
        // RFC4843 https://tools.ietf.org/html/rfc4843
        // An IPv6 Prefix for Overlay Routable Cryptographic Hash Identifiers
        // 2001:10::/28 prefix
        if (b[0] == 0x20 && b[1] == 0x01 && b[2] == 0x00 && (b[3] & 0xF0) == 0x10)
        {
            return false;
        }
    }
    return true;
}

inline std::string ToHexString(const unsigned char *p,std::size_t size)
{
    const char hexc[17] = "0123456789abcdef";
    char hex[128];
    std::string strHex;
    strHex.reserve(size * 2);

    for (size_t i = 0;i < size;i += 64)
    {
        size_t k;
        for (k = 0;k < 64 && k + i < size;k++)
        {
            int c = *p++;
            hex[k * 2]     = hexc[c >> 4];
            hex[k * 2 + 1] = hexc[c & 15];
        }
        strHex.append(hex,k * 2);
    }
    return strHex;    
}

inline std::string ToHexString(const std::vector<unsigned char>& vch)
{
    return ToHexString(&vch[0],vch.size());
}

template<typename T>
inline std::string UIntToHexString(const T& t)
{
    const char hexc[17] = "0123456789abcdef";
    char hex[sizeof(T) * 2 + 1];
    for (std::size_t i = 0;i < sizeof(T);i++)
    {
        int byte = (t >> ((sizeof(T) - i - 1)) * 8) & 0xFF;
        hex[i * 2]     = hexc[byte >> 4];
        hex[i * 2 + 1] = hexc[byte & 15];
    }
    hex[sizeof(T) * 2] = 0;
    return std::string(hex);
}

inline int CharToHex(char c)
{
    if (c >= '0' && c <= '9') return (c - '0');
    if (c >= 'a' && c <= 'f') return (c - 'a' + 10);
    if (c >= 'A' && c <= 'F') return (c - 'A' + 10);
    return -1;
}

inline std::vector<unsigned char> ParseHexString(const char* psz)
{
    std::vector<unsigned char> vch;
    vch.reserve(128);
    while (*psz)
    {
        int h = CharToHex(*psz++);
        int l = CharToHex(*psz++);
        if (h < 0 || l < 0) break;
        vch.push_back((unsigned char)((h << 4) | l));
    }
    return vch; 
}

inline std::size_t ParseHexString(const char* psz,unsigned char* p,std::size_t n)
{
    unsigned char* end = p + n;
    while (*psz && p != end)
    {
        int h = CharToHex(*psz++);
        int l = CharToHex(*psz++);
        if (h < 0 || l < 0) break;
        *p++ = (unsigned char)((h << 4) | l);
    }
    return (n - (end - p));
}

inline std::vector<unsigned char> ParseHexString(const std::string& str)
{
    return ParseHexString(str.c_str());
}

inline std::size_t ParseHexString(const std::string& str,unsigned char* p,std::size_t n)
{
    return ParseHexString(str.c_str(),p,n);
}


inline bool IsSuperNodeInnerNonce(uint64 nNonce)
{
    return nNonce == SUPERNODE_INNER_NONCE;
}

#ifdef __GNUG__
#include <cxxabi.h>
inline const char* TypeName(const std::type_info& info)
{
    int status = 0;
    return abi::__cxa_demangle(info.name(), 0, 0, &status);
}
#else
inline const char* TypeName(const std::type_info& info)
{
    return info.name();
}
#endif

} // namespace walleve

#endif //WALLEVE_UTIL_H

