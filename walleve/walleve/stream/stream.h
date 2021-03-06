// Copyright (c) 2016-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef  WALLEVE_STREAM_H
#define  WALLEVE_STREAM_H

#include "walleve/type.h"
#include "walleve/stream/circular.h"

#include <iostream>
#include <fstream>
#include <iomanip>
#include <boost/type_traits.hpp>
#include <boost/asio.hpp>

namespace walleve
{

enum
{
    WALLEVE_STREAM_SAVE,
    WALLEVE_STREAM_LOAD
};

typedef const boost::true_type  BasicType;
typedef const boost::false_type ObjectType;

typedef const boost::integral_constant<int, WALLEVE_STREAM_SAVE> SaveType;
typedef const boost::integral_constant<int, WALLEVE_STREAM_LOAD> LoadType;

// Base class of serializable stream
class CWalleveStream
{
public:
    CWalleveStream(std::streambuf* sb) : ios(sb) {}

    virtual std::size_t GetSize() {return 0;}
    
    std::iostream& GetIOStream()
    {
        return ios;
    }

    CWalleveStream& Write(const char *s,std::size_t n)
    {
        ios.write(s,n);
        return (*this);
    }

    CWalleveStream& Read(char *s,std::size_t n)
    {
        ios.read(s,n);
        return (*this);
    }

    template <typename T,typename O>
    CWalleveStream& Serialize(T& t,O &opt)
    {
        return Serialize(t,boost::is_fundamental<T>(),opt);
    }

    template <typename T>
    CWalleveStream& operator<< (const T& t)
    {
        return Serialize(const_cast<T&>(t),boost::is_fundamental<T>(),SaveType());
    }

    template <typename T>
    CWalleveStream& operator>> (T& t)
    {
        return Serialize(t, boost::is_fundamental<T>(),LoadType());
    }

    template <typename T>
    std::size_t GetSerializeSize(const T& t)
    {
        std::size_t serSize = 0;
        Serialize(const_cast<T&>(t),boost::is_fundamental<T>(),serSize);
        return serSize;
    }

protected:
    template <typename T>
    CWalleveStream& Serialize(const T& t,BasicType&,SaveType&)
    {
        return Write((const char *)&t,sizeof(t));
    }

    template <typename T>
    CWalleveStream& Serialize(T& t,BasicType&,LoadType&)
    {
        return Read((char *)&t,sizeof(t));
    }

    template <typename T>
    CWalleveStream& Serialize(const T& t,BasicType&,std::size_t& serSize)
    {
        serSize += sizeof(t);
        return (*this);
    }

    template <typename T,typename O>
    CWalleveStream& Serialize(T& t,ObjectType&,O& opt)
    {
        t.WalleveSerialize(*this,opt);
        return (*this);
    }

    /* std::string */
    CWalleveStream& Serialize(std::string& t,ObjectType&,SaveType&);
    CWalleveStream& Serialize(std::string& t,ObjectType&,LoadType&);
    CWalleveStream& Serialize(std::string& t,ObjectType&,std::size_t& serSize);

    /* std::vector */
    template<typename T, typename A>
    CWalleveStream& Serialize(const std::vector<T, A>& t,ObjectType&,SaveType&);
    template<typename T, typename A>
    CWalleveStream& Serialize(std::vector<T, A>& t,ObjectType&,SaveType&);
    template<typename T, typename A>
    CWalleveStream& Serialize(std::vector<T, A>& t,ObjectType&,LoadType&);
    template<typename T, typename A>
    CWalleveStream& Serialize(const std::vector<T, A>& t,ObjectType&,std::size_t& serSize);
    template<typename T, typename A>
    CWalleveStream& Serialize(std::vector<T, A>& t,ObjectType&,std::size_t& serSize);

    /* std::map */
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(const std::map<K, V, C, A>& t,ObjectType&,SaveType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::map<K, V, C, A>& t,ObjectType&,SaveType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::map<K, V, C, A>& t,ObjectType&,LoadType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(const std::map<K, V, C, A>& t,ObjectType&,std::size_t& serSize);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::map<K, V, C, A>& t,ObjectType&,std::size_t& serSize);

    /* std::multimap */
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(const std::multimap<K, V, C, A>& t,ObjectType&,SaveType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::multimap<K, V, C, A>& t,ObjectType&,SaveType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::multimap<K, V, C, A>& t,ObjectType&,LoadType&);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(const std::multimap<K, V, C, A>& t,ObjectType&,std::size_t& serSize);
    template<typename K, typename V, typename C, typename A>
    CWalleveStream& Serialize(std::multimap<K, V, C, A>& t,ObjectType&,std::size_t& serSize);

    /* std::pair */
    template<typename P1, typename P2, typename O>
    CWalleveStream& Serialize(std::pair<P1, P2>& t,ObjectType&,O& o);
protected:
    std::iostream ios;
};

// Autosize buffer stream
class CWalleveBufStream : public boost::asio::streambuf, public CWalleveStream
{
public:
    CWalleveBufStream() : CWalleveStream(this) {}

    void Clear()
    {
        ios.clear();
        consume(size());
    }

    char *GetData() const
    {
        return gptr();
    }

    std::size_t GetSize()
    {
        return size();
    }

    void HexToString(std::string& strHex)
    {
        const char hexc[17] = "0123456789abcdef";
        char strByte[4] = "00 ";
        strHex.clear();
        strHex.reserve(size() * 3);
        char *p = gptr();
        while(p != pptr())
        {
            int c = (int)((unsigned char *)p++)[0];
            strByte[0] = hexc[c >> 4];
            strByte[1] = hexc[c & 15];
            strHex.append(strByte);
        }
    }

    void Dump()
    {
        std::cout << "CWalleveStream Dump : " << size() << std::endl << std::hex;
        char *p = gptr();
        int n = 0;
        std::cout.setf(std::ios_base::hex);
        while(p != pptr())
        {
            std::cout << std::setfill('0') << std::setw(2) << (int)((unsigned char *)p++)[0] << " ";
            if (++n == 32)
            {
                std::cout << std::endl;
                n = 0;
            }
        }
        std::cout.unsetf(std::ios::hex);
        if (n != 0)
        {
            std::cout << std::endl;
        }
    }

    friend CWalleveStream& operator<< (CWalleveStream& s,CWalleveBufStream& ssAppend)
    {
        return s.Write(ssAppend.gptr(),ssAppend.GetSize());
    }

    friend CWalleveStream& operator>> (CWalleveStream& s,CWalleveBufStream& ssSink)
    {
        std::size_t len = s.GetSize();
        ssSink.prepare(len);
        s.Read(ssSink.pptr(),len);
        ssSink.commit(len);
        return s;
    }
};

// Circular buffer stream
class CWalleveCircularStream : public circularbuf, public CWalleveStream
{
public:
    CWalleveCircularStream(std::size_t nMaxSize)
    : circularbuf(nMaxSize) ,CWalleveStream(this) {}

    void Clear()
    {
        ios.clear();
        consume(size());
    }

    std::size_t GetSize()
    {
        return size();
    }

    std::size_t GetBufFreeSpace() const
    {
        return freespace();
    }

    std::size_t GetWritePos() const
    {
        return putpos();
    }

    bool Seek(std::size_t nPos)
    {
        ios.clear();
        return (seekpos(nPos) >= 0);
    }

    void Rewind()
    {
        ios.clear();
        seekoff(0,std::ios_base::beg);
    }

    void Consume(std::size_t nSize)
    {
        consume(nSize);
    }

    void Dump()
    {
        std::cout << "CWalleveStream Dump : " << size() << std::endl << std::hex;
        seekoff(0,std::ios_base::beg);

        int n = 0;
        std::cout.setf(std::ios_base::hex);
        while(in_avail() != 0)
        {
            int c = sbumpc();

            std::cout << std::setfill('0') << std::setw(2) << c << " ";
            if (++n == 32)
            {
                std::cout << std::endl;
                n = 0;
            }
        }
        std::cout.unsetf(std::ios::hex);
        if (n != 0)
        {
            std::cout << std::endl;
        }
    }
};

// File stream with compatible serialization mothed
class CWalleveFileStream : public std::filebuf, public CWalleveStream
{

public:
    CWalleveFileStream(const char* filename) : CWalleveStream(this)
    {
        open(filename,std::ios_base::in | std::ios_base::out
                      | std::ios_base::binary);
    }
    ~CWalleveFileStream()
    {
        close();
    }

    bool IsValid() const
    {
        return is_open();
    }

    bool IsEOF() const
    {
        return ios.eof();
    }

    std::size_t GetSize()
    {
        std::streampos cur = seekoff(0,std::ios_base::cur);
        std::size_t size = (std::size_t)(seekoff(0,std::ios_base::end) - cur);
        seekpos(cur);
        return size;
    }

    std::size_t GetCurPos()
    {
        return (std::size_t)seekoff(0,std::ios_base::cur);
    }

    void Seek(std::size_t pos)
    {
        seekpos((std::streampos)pos);
    }

    void SeekToBegin()
    {
        seekoff(0,std::ios_base::beg);
    }

    void SeekToEnd()
    {
        seekoff(0,std::ios_base::end);
    }

    void Sync()
    {
        sync();
    }
};

// R/W compact size
//  size <  253        -- 1 byte
//  size <= USHRT_MAX  -- 3 bytes  (253 + 2 bytes)
//  size <= UINT_MAX   -- 5 bytes  (254 + 4 bytes)
//  size >  UINT_MAX   -- 9 bytes  (255 + 8 bytes)
class CVarInt
{
    friend class CWalleveStream;
public:
    CVarInt() : nValue(0) {}
    CVarInt(uint64 ValueIn) : nValue(ValueIn) {}
protected:
    void WalleveSerialize(CWalleveStream& s,SaveType&);
    void WalleveSerialize(CWalleveStream& s,LoadType&);
    void WalleveSerialize(CWalleveStream& s,std::size_t& serSize);
public:
    uint64 nValue;
};

// Binary memory 
class CBinary
{
    friend class CWalleveStream;
public:
    CBinary(char *pBufferIn,std::size_t nLengthIn) : pBuffer(pBufferIn),nLength(nLengthIn) {}
    friend bool operator==(const CBinary& a,const CBinary& b)
    {
        return (a.nLength == b.nLength
                && (a.nLength == 0 || std::memcmp(a.pBuffer,b.pBuffer,a.nLength) == 0));
    }
    friend bool operator!=(const CBinary& a,const CBinary& b)
    {
        return (!(a == b));
    }
protected:
    void WalleveSerialize(CWalleveStream& s,SaveType&);
    void WalleveSerialize(CWalleveStream& s,LoadType&);
    void WalleveSerialize(CWalleveStream& s,std::size_t& serSize);

protected:
    char *pBuffer;
    std::size_t nLength;
};

/* CWalleveStream vector serialize impl */
template<typename T, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::vector<T, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    if (boost::is_fundamental<T>::value)
    {
        Write((char *)&t[0],sizeof(T) * t.size());
    }
    else
    {
        for (uint64 i = 0;i < t.size();i++)
        {
            *this << t[i];
        }
    }
    return (*this);
}

template<typename T, typename A>
CWalleveStream& CWalleveStream::Serialize(std::vector<T, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    if (boost::is_fundamental<T>::value)
    {
        Write((char *)&t[0],sizeof(T) * t.size());
    }
    else
    {
        for (uint64 i = 0;i < t.size();i++)
        {
            *this << t[i];
        }
    }
    return (*this);
}

template<typename T, typename A>
CWalleveStream& CWalleveStream::Serialize(std::vector<T, A>& t,ObjectType&,LoadType&)
{
    CVarInt var;
    *this >> var;
    t.resize(var.nValue);
    if (boost::is_fundamental<T>::value)
    {
        Read((char *)&t[0],sizeof(T) * t.size());
    }
    else
    {
        for (uint64 i = 0;i < var.nValue;i++)
        {
            *this >> t[i];
        }
    }
    return (*this);
}

template<typename T, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::vector<T, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    if (boost::is_fundamental<T>::value)
    {
        serSize += sizeof(T) * t.size();
    }
    else
    {
        for (uint64 i = 0;i < t.size();i++)
        {
            serSize += GetSerializeSize(t[i]);
        }
    }
    return (*this);
}

template<typename T, typename A>
CWalleveStream& CWalleveStream::Serialize(std::vector<T, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    if (boost::is_fundamental<T>::value)
    {
        serSize += sizeof(T) * t.size();
    }
    else
    {
        for (uint64 i = 0;i < t.size();i++)
        {
            serSize += GetSerializeSize(t[i]);
        }
    }
    return (*this);
}

/* CWalleveStream map serialize impl */
template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::map<K, V, C, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    for (typename std::map<K, V, C, A>::const_iterator it = t.begin(); it != t.end(); ++it)
    {
        *this << (*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::map<K, V, C, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    for (typename std::map<K, V, C, A>::iterator it = t.begin(); it != t.end(); ++it)
    {
        *this << (*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::map<K, V, C, A>& t,ObjectType&,LoadType&)
{
    CVarInt var;
    *this >> var;
    for (uint64 i = 0;i < var.nValue;i++)
    {
        std::pair<K, V> item;
        *this >> item;
        t.insert(item); 
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::map<K, V, C, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    for (typename std::map<K, V, C, A>::const_iterator it = t.begin(); it != t.end(); ++it)
    {
        serSize += GetSerializeSize(*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::map<K, V, C, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    for (typename std::map<K, V, C, A>::iterator it = t.begin(); it != t.end(); ++it)
    {
        serSize += GetSerializeSize(*it);
    }
    return (*this);
}

/* CWalleveStream multimap serialize impl */
template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::multimap<K, V, C, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    for (typename std::multimap<K, V, C, A>::const_iterator it = t.begin(); it != t.end(); ++it)
    {
        *this << (*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::multimap<K, V, C, A>& t,ObjectType&,SaveType&)
{
    *this << CVarInt(t.size());
    for (typename std::multimap<K, V, C, A>::iterator it = t.begin(); it != t.end(); ++it)
    {
        *this << (*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::multimap<K, V, C, A>& t,ObjectType&,LoadType&)
{
    CVarInt var;
    *this >> var;
    for (uint64 i = 0;i < var.nValue;i++)
    {
        std::pair<K, V> item;
        *this >> item;
        t.insert(item); 
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(const std::multimap<K, V, C, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    for (typename std::multimap<K, V, C, A>::const_iterator it = t.begin(); it != t.end(); ++it)
    {
        serSize += GetSerializeSize(*it);
    }
    return (*this);
}

template<typename K, typename V, typename C, typename A>
CWalleveStream& CWalleveStream::Serialize(std::multimap<K, V, C, A>& t,ObjectType&,std::size_t& serSize)
{
    CVarInt var(t.size());
    serSize += GetSerializeSize(var);
    for (typename std::multimap<K, V, C, A>::iterator it = t.begin(); it != t.end(); ++it)
    {
        serSize += GetSerializeSize(*it);
    }
    return (*this);
}

/* CWalleveStream pair serialize impl */
template<typename P1, typename P2, typename O>
CWalleveStream& CWalleveStream::Serialize(std::pair<P1, P2>& t,ObjectType&,O& o)
{
    return Serialize(t.first,o).Serialize(t.second,o);
}

template<typename T>
std::size_t GetSerializeSize(const T& obj)
{
    CWalleveBufStream ss;
    return ss.GetSerializeSize(obj);
}

} // namespace walleve

#endif //WALLEVE_STREAM_H

