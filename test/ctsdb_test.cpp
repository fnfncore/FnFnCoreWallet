// Copyright (c) 2017-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <boost/test/unit_test.hpp>

#include "test_fnfn.h"
#include "ctsdb.h"
#include "walleve/walleve.h"
#include "crypto.h"
#include "uint256.h"


BOOST_FIXTURE_TEST_SUITE(ctsdb_tests, BasicUtfSetup)

using namespace multiverse::storage;

class CMetaData
{
    friend class walleve::CWalleveStream;
public:
    uint224 hash;
    uint32  file;
    uint32  offset;
    uint32  blocktime;
protected:
    template <typename O>
    void WalleveSerialize(walleve::CWalleveStream& s,O& opt)
    {
        s.Serialize(hash,opt);
        s.Serialize(file,opt);
        s.Serialize(offset,opt);
        s.Serialize(blocktime,opt);
    }
};

typedef CCTSDB<uint224,CMetaData,CCTSChunkSnappy<uint224,CMetaData> > CMetaDB;
//typedef CCTSDB<uint224,CMetaData> CMetaDB;

BOOST_AUTO_TEST_CASE( ctsdb )
{
    CMetaDB db;
    BOOST_CHECK( db.Initialize(boost::filesystem::path("/home/xdwang/test")) );

    db.RemoveAll();

    std::vector<std::pair<int64,uint224> > vTest;
    for (int loop = 0;loop < 1;loop++)
    {
        for (int i = 0;i < 3600;i++)
        {
            int64 nTime = loop * 3600 + i;
            for (int j = 0;j < 10000;j++)
            {
                uint256 txid;
                multiverse::crypto::CryptoGetRand256(txid);
                
                CMetaData data;
                data.hash = uint224(txid);
                data.file = 1;
                data.offset = i * j;
                data.blocktime = nTime;
                
                db.Update(nTime,data.hash,data);
                if (i == j)
                {
                    vTest.push_back(std::make_pair(nTime,data.hash));
                }
            }
        }
        walleve::CTicks t1;
        BOOST_CHECK(  db.Flush() );
        walleve::CTicks t2;
        BOOST_CHECK(  db.Flush() );
        std::cout << "Flush : " << (t2 - t1) << " " << (t2.Elapse() / 1000) << "\n";
    }

    {
        walleve::CTicks t;
        for (int i = 0;i < vTest.size();i++)
        {
            CMetaData data;
            BOOST_CHECK( db.Retrieve(vTest[i].first, vTest[i].second, data) );
            BOOST_CHECK( data.hash == vTest[i].second );            
        }

        std::cout << "Retrieve : " << (t.Elapse() / vTest.size()) << "\n";
    }

    db.Deinitialize();
}

BOOST_AUTO_TEST_SUITE_END()
