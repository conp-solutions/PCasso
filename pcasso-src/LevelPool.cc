#include "LevelPool.h"

#include <sstream>

using namespace davide;
using namespace std;
using namespace Minisat;

LevelPool::LevelPool(int _max_size)
{
    full          = false;
    writeP        = 0;
    endP          = 0;
    levelPoolLock = RWLock();
    max_size      = (unsigned int)_max_size; // Davide> Safe, _max_size < INT_MAX
    shared_clauses.growTo((_max_size * 1000) / 4, lit_Undef);
}

bool LevelPool::add_shared(vec<Lit>& lits, unsigned int nodeID, bool disable_dupl_removal, bool disable_dupl_check)
{

    vec<Lit> temp; // FIXME: replace with a write of node ID to first writable position
    temp.push(lit_Undef);
    for (int i = 0; i < lits.size(); i++) {
        temp.push(lits[i]);
    }

    assert(temp[0] == lit_Undef);

    int i = 0;
    
    std::stringstream msg;
    msg << "c LP node " << nodeID << " beging add_shared with writeP: " << writeP << " endP: " << endP << " and " << lits.size() << " lits" << endl;
    std::cerr << msg.str();

    temp[0] = toLit(nodeID);
    
    assert(toInt(temp[0]) >= 0 && "the number to identify the node should be positive");
    assert(writeP == 0 || shared_clauses[writeP-1] == lit_Undef); // the pointer should point at the end of a clause

    assert(temp.size() < shared_clauses.size());

    if (writeP + temp.size() < shared_clauses.size() - 2) { // Space for the ending lit_Undef
        for (i = 0; i < temp.size(); ++i) {
            shared_clauses[writeP + i] = temp[i];
        }
        writeP += temp.size();
        int k = writeP;
        ++writeP;
        while (shared_clauses[k] != lit_Undef && k < endP) { // clean the whole vector, or until the next end of a clause
            shared_clauses[k++] = lit_Undef;
        }
        if (writeP > endP) { endP = writeP; }
    } else { // write from the beginning
        Debug::PRINTLN_NOTE("write from beginning!");
        full = true;

        endP = writeP;
        assert(shared_clauses[endP - 1] == lit_Undef);

        for (writeP = 0; writeP < temp.size(); ++writeP) {
            shared_clauses[writeP] = temp[writeP];
        }
        int k = writeP;
        ++writeP;
        while (shared_clauses[k] != lit_Undef && k < endP) {
            shared_clauses[k++] = lit_Undef;
        }
        assert(endP > writeP);
    }
    msg.str("");
    msg << "c LP node " << nodeID << " end shared with writeP: " << writeP << " endP: " << endP << " and " << lits.size() << " lits" << endl;
    std::cerr << msg.str();
    
    return true;
}
void
LevelPool::getChunk(int readP, vec<Lit>& chunk)
{
    assert(writeP == 0 || shared_clauses[writeP - 1] == lit_Undef);

    if (readP >= endP) { return; }

    if (( (readP != 0 && shared_clauses[readP - 1] == lit_Undef) || readP == 0)) {
        if (readP <= writeP) {
            chunk.growTo(writeP - readP);
            int j = 0;
	    assert(readP == 0 || toInt(shared_clauses[readP]) >= 0); // the first literal indicates the ID of the node that shared the clause
            for (int i = readP; i < writeP; ++i) {
                assert(writeP - readP == chunk.size());
                assert(j < chunk.size());
                chunk[j++] = shared_clauses[i];
            }
            assert(chunk.size() == j);
            assert(j == 0 || chunk[j - 1] == lit_Undef);
        } else {
            chunk.growTo((endP - readP) + writeP);
            int j = 0;
	    assert(readP == 0 || toInt(shared_clauses[readP]) >= 0); // the first literal indicates the ID of the node that shared the clause
            for (int i = readP; i < endP; ++i) {
                assert(j < chunk.size());
                chunk[j++] = shared_clauses[i];
            }
            for (int i = 0; i < writeP; ++i) {
                assert(j < chunk.size());
                chunk[j++] = shared_clauses[i];
            }
            assert(chunk.size() == j);
            assert(j == 0 || chunk[j - 1] == lit_Undef);
        }
    } else {
        chunk.growTo(writeP);
        int j = 0;
	assert(writeP == 0 || toInt(shared_clauses[0]) > 0); // the first literal indicates the ID of the node that shared the clause
        for (int i = 0; i < writeP; ++i) {
            assert(j < chunk.size());
            chunk[j++] = shared_clauses[i];
        }
        assert(chunk.size() == j);
        assert(j == 0 || chunk[j - 1] == lit_Undef);
    }
    // The else case is not strictly necessary. The clauses will be read at next
    // iteration, even thoug some will be missed.
}
