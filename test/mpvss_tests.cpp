// Copyright (c) 2017-2019 The Multiverse developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <boost/test/unit_test.hpp>

#include "test_fnfn.h"
#include "mpvss.h"
#include "mpinterpolation.h"

using curve25519::Print32;

BOOST_FIXTURE_TEST_SUITE(mpvss_tests, BasicUtfSetup)

void RandGeneretor(uint8_t* p)
{
    for (int i = 0; i < 32; i++)
    {
        *p++ = rand();
    }
}

void KeyGenerator(uint256& priv, uint256& pub)
{
    uint8_t md32[32];

    RandGeneretor(md32);
    md32[31] &= 0x0F;
    memcpy(priv.begin(), md32, 32);

    CEdwards25519 P;
    P.Generate(priv);
    P.Pack(pub.begin());
}

BOOST_AUTO_TEST_CASE( fp25519 )
{
    srand(time(0));
    uint8_t md32[32];

    // add, minus
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CFP25519 add1(md32);
        RandGeneretor(md32);
        CFP25519 add2(md32);
        CFP25519 fpSum = add1 + add2;
        BOOST_CHECK( add1 == fpSum - add2 );
        BOOST_CHECK( add2 == fpSum - add1 );
    }

    // multiply, divide
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CFP25519 mul1(md32);
        RandGeneretor(md32);
        CFP25519 mul2(md32);
        CFP25519 fpProduct = mul1 * mul2;
        BOOST_CHECK( mul1 == fpProduct / mul2 );
        BOOST_CHECK( mul2 == fpProduct / mul1 );
    }

    // inverse
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CFP25519 fp(md32);
        CFP25519 fpInverse = fp.Inverse();
        BOOST_CHECK( CFP25519(1) == fp * fpInverse );
    }

    // sqrt square
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CFP25519 fp1(md32);
        CFP25519 fp2(md32);
        fp2 = fp2.Square().Sqrt();
        BOOST_CHECK( fp2.Square() == fp1.Square() );
    }
}

BOOST_AUTO_TEST_CASE( sc25519 )
{
    srand(time(0));
    uint8_t md32[32];

    // add, minus
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CSC25519 add1(md32);
        RandGeneretor(md32);
        CSC25519 add2(md32);
        CSC25519 scSum = add1 + add2;
        BOOST_CHECK( add1 == scSum - add2 );
        BOOST_CHECK( add2 == scSum - add1 );
    }

    // multiply
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CSC25519 sc(md32);
        RandGeneretor(md32);
        uint32_t n = 10;
        CSC25519 scProduct = sc * n;
        for (int i = 0; i < n - 1; i++)
        {
            scProduct -= sc;
        }
        BOOST_CHECK( scProduct == sc );
    }

    // negative
    for (int i = 0; i < 10; i++)
    {
        RandGeneretor(md32);
        CSC25519 sc(md32);
        CSC25519 scNegative1 = -sc;
        CSC25519 scNegative2(sc);
        scNegative2.Negative();
        BOOST_CHECK( scNegative1 == scNegative2 );
        BOOST_CHECK( CSC25519() == sc + scNegative1 );
    }
}

BOOST_AUTO_TEST_CASE( ed25519 )
{
    srand(time(0));
    uint8_t md32[32];

    // sign, verify
    for (int i = 0; i < 10; i++)
    {
        uint256 priv1, pub1;
        uint256 priv2, pub2;
        KeyGenerator(priv1, pub1);
        KeyGenerator(priv2, pub2);

        RandGeneretor(md32);
        CSC25519 hash(md32);

        CSC25519 sign = CSC25519(priv1.begin()) + CSC25519(priv2.begin()) * hash;

        CEdwards25519 P,R,S;
        P.Unpack(pub1.begin());
        R.Unpack(pub2.begin());
        S.Generate(sign);
        
        BOOST_CHECK( S == (P + R.ScalarMult(hash)) );
    }
}

BOOST_AUTO_TEST_CASE( interpolation )
{
    srand(time(0));
    uint8_t md32[32];

    // lagrange, newton
    for (int i = 0; i < 1; i++)
    {
        std::vector<uint32_t> vX;
        for (int i = 1; i < 51; i++)
        {
            vX.push_back(i);
        }

        std::vector<std::pair<uint32_t,uint256> > vShare;
        for (int i = 0; i < 26; i++)
        {
            int index = rand() % vX.size();
            uint32_t x = vX[index];
            vX.erase(vX.begin() + index);

            RandGeneretor(md32);
            uint256 y((uint64_t*)md32);
            vShare.push_back(std::make_pair(x, y));
        }

        BOOST_CHECK( MPLagrange(vShare) == MPNewton(vShare) );
    }
}

BOOST_AUTO_TEST_CASE( mpvss )
{
    srand(time(0));
    for (size_t count = 50; count <= 50; count++)
    {
        uint256 nInitValue;
        std::vector<uint256> vID;
        std::map<uint256,CMPSecretShare> mapSS;
        std::vector<CMPSealedBox> vSBox;
        std::vector<CMPCandidate> vCandidate;

        CMPSecretShare ssWitness;

        boost::posix_time::ptime t0;
        std::cout << "Test mpvss begin: count " << count << "\n{\n";
        vID.resize(count); vSBox.resize(count); vCandidate.resize(count);
        //Setup
        t0 = boost::posix_time::microsec_clock::universal_time();
        for (int i = 0;i < count;i++)
        {
            vID[i] = uint256(i + 1);
            mapSS[vID[i]] = CMPSecretShare(vID[i]);

            mapSS[vID[i]].Setup(count + 1,vSBox[i]);
            vCandidate[i] = CMPCandidate(vID[i],1,vSBox[i]);

            nInitValue = nInitValue ^ mapSS[vID[i]].myBox.vCoeff[0];
        }
        std::cout << "\tSetup : " << ((boost::posix_time::microsec_clock::universal_time() - t0).ticks() / count) <<"\n";
        std::cout << "\tInit value = " << nInitValue.GetHex() << "\n";
        {
            CMPSealedBox box;
            ssWitness.Setup(count + 1,box);
        }

        //Enroll
        t0 = boost::posix_time::microsec_clock::universal_time();
        for (int i = 0;i < count;i++)
        {   
            mapSS[vID[i]].Enroll(vCandidate);
        }
        std::cout << "\tEnroll : " << ((boost::posix_time::microsec_clock::universal_time() - t0).ticks() / count) <<"\n";
        ssWitness.Enroll(vCandidate);

        // Distribute
        t0 = boost::posix_time::microsec_clock::universal_time();
        for (int i = 0;i < count;i++)
        {
            std::map<uint256,std::vector<uint256> > mapShare;
            mapSS[vID[i]].Distribute(mapShare);
            for (int j = 0;j < count;j++)
            {
                if (i != j)
                {
                    BOOST_CHECK( mapSS[vID[j]].Accept(vID[i],mapShare[vID[j]]) );
                }
            }
        }
        std::cout << "\tDistribute : " << ((boost::posix_time::microsec_clock::universal_time() - t0).ticks() / count) <<"\n";

        // Publish
        t0 = boost::posix_time::microsec_clock::universal_time();
        std::vector< std::map<uint256,std::vector<uint256> > > vecMapShare;
        vecMapShare.resize(count);
        for (int i = 0;i < count;i++)
        {
            mapSS[vID[i]].Publish(vecMapShare[i]);
        }

        for (int i = 0;i < count;i++)
        {
            bool fCompleted = false;
            for (int j = 0;j < count;j++)
            {
                int indexFrom = (i + j) % count;
                BOOST_CHECK( mapSS[vID[i]].Collect(vID[indexFrom], vecMapShare[indexFrom], fCompleted) );
            }
            BOOST_CHECK( fCompleted );
        }

        bool fCompleted = false;
        for (int i = 0; i < count; i++)
        {
            BOOST_CHECK( ssWitness.Collect(vID[i],vecMapShare[i],fCompleted) );
        }
        BOOST_CHECK( fCompleted );

        std::cout << "\tPublish : " << ((boost::posix_time::microsec_clock::universal_time() - t0).ticks() / count) <<"\n";

        // Reconstruct 
        t0 = boost::posix_time::microsec_clock::universal_time();
        for (int i = 0;i < count;i++)
        {
            uint256 nRecValue;
            std::map<uint256,std::pair<uint256,std::size_t> > mapSecret;
            mapSS[vID[i]].Reconstruct(mapSecret);
            for (std::map<uint256,std::pair<uint256,std::size_t> >::iterator it = mapSecret.begin();it != mapSecret.end();++it)
            {
                nRecValue = nRecValue ^ (*it).second.first;
            }
            std::cout << "\tReconstruct candidate " << i << " : " << nRecValue.GetHex() << "\n";
            BOOST_CHECK( nRecValue == nInitValue );
        }
        std::cout << "\tReconstruct : " << ((boost::posix_time::microsec_clock::universal_time() - t0).ticks() / count) <<"\n";;

        uint256 nRecValue;
        std::map<uint256,std::pair<uint256,std::size_t> > mapSecret;
        ssWitness.Reconstruct(mapSecret);
        for (std::map<uint256,std::pair<uint256,std::size_t> >::iterator it = mapSecret.begin();it != mapSecret.end();++it)
        {
            nRecValue = nRecValue ^ (*it).second.first;
        }
        std::cout << "\tReconstruct witness : " << nRecValue.GetHex() << "\n";
        std::cout << "}\n";

        BOOST_CHECK( nRecValue == nInitValue );
    }
}

BOOST_AUTO_TEST_CASE( generate_pow_code )
{
    std::cout << "{" << std::endl;
    for (int i = 1; i <= 51; i++)
    {
        std::cout << "    // " << i << "^1 ... " << i << "^26" << std::endl;
        std::cout << "    {" << std::endl;
        CSC25519 base(1);
        uint256 ret;
        for (int j = 1; j <= 26; j++)
        {
            base *= i;
            base.Pack(ret.begin());
            const uint64* p = (const uint64*)ret.begin();
            std::cout << "        CSC25519({";
            for (int k = 0; k < 4; k++)
            {
                std::cout << "0x" << std::hex << *p++ << std::resetiosflags(std::ios_base::basefield);
                if (k < 3)
                {
                    std::cout << ",";
                }
            }
            std::cout << "})," << std::endl;
        }
        std::cout << "    }," << std::endl;
    }
    std::cout << "};" << std::endl;
}

BOOST_AUTO_TEST_SUITE_END()