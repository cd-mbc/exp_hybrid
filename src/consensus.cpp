/**
 * Copyright 2018 VMware
 * Copyright 2018 Ted Yin
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <cassert>
#include <stack>

#include "hotstuff/util.h"
#include "hotstuff/consensus.h"

#define LOG_INFO HOTSTUFF_LOG_INFO
#define LOG_DEBUG HOTSTUFF_LOG_DEBUG
#define LOG_WARN HOTSTUFF_LOG_WARN
#define LOG_PROTO HOTSTUFF_LOG_PROTO

namespace hotstuff {

/* The core logic of HotStuff, is fairly simple :). */
/*** begin HotStuff protocol logic ***/
HotStuffCore::HotStuffCore(ReplicaID id,
                            privkey_bt &&priv_key,
                            int blk_size,
                            double delta):
        b0(new Block(true, 1, true)),
        b_lock(b0),
        b_exec(b0),
        vheight(0),
        priv_key(std::move(priv_key)),
        tails{b0},
        vote_disabled(false),
        id(id),
        blk_size(blk_size),
        delta(delta),
        storage(new EntityStorage()) {
    storage->add_blk(b0);
}

void HotStuffCore::sanity_check_delivered(const block_t &blk) {
    if (!blk->delivered)
        throw std::runtime_error("block not delivered");
}

block_t HotStuffCore::get_delivered_blk(const uint256_t &blk_hash) {
    block_t blk = storage->find_blk(blk_hash);
    if (blk == nullptr || !blk->delivered)
        throw std::runtime_error("block not delivered");
    return blk;
}

bool HotStuffCore::on_deliver_blk(const block_t &blk) {
    if (blk->delivered)
    {
        LOG_WARN("attempt to deliver a block twice");
        return false;
    }
    blk->parents.clear();
    for (const auto &hash: blk->parent_hashes)
        blk->parents.push_back(get_delivered_blk(hash));
    blk->height = blk->parents[0]->height + 1;

    if (blk->qc)
    {
        block_t _blk = storage->find_blk(blk->qc->get_obj_hash());
        if (_blk == nullptr)
            throw std::runtime_error("block referred by qc not fetched");
        blk->qc_ref = std::move(_blk);
    } // otherwise blk->qc_ref remains null

    for (auto pblk: blk->parents) tails.erase(pblk);
    tails.insert(blk);

    blk->delivered = true;
    LOG_DEBUG("deliver %s", std::string(*blk).c_str());
    return true;
}

void HotStuffCore::update_hqc(const block_t &_hqc, const quorum_cert_bt &qc) {
    if (_hqc->height > hqc.first->height)
    {
        hqc = std::make_pair(_hqc, qc->clone());
        on_hqc_update();
    }
}

void HotStuffCore::update(const block_t &blk) {
    
    std::vector<block_t> commit_queue;
    block_t b;
    for (b = blk; b->height > b_exec->height; b = b->parents[0])
    { /* TODO: also commit the uncles/aunts */
        commit_queue.push_back(b);
    }
    if (b != b_exec)
        throw std::runtime_error("safety breached :( " +
                                std::string(*blk) + " " +
                                std::string(*b_exec));
    for (auto it = commit_queue.rbegin(); it != commit_queue.rend(); it++)
    {
        const block_t &blk = *it;
        blk->decision = 1;
        LOG_PROTO("commit %s", std::string(*blk).c_str());
        for (size_t i = 0; i < blk->cmds.size(); i++) {
            do_decide(Finality(id, 1, i, blk->height,
                                blk->cmds[i], blk->get_hash()));
        }                        
    }
    b_exec = blk;
}

block_t HotStuffCore::on_propose(const std::vector<uint256_t> &cmds,
                            const std::vector<block_t> &parents,
                            bytearray_t &&extra) {
    if (parents.empty())
        throw std::runtime_error("empty parents");
    
    std::vector<uint256_t> p_cmds;
    int cmd_pool_size = cmd_pool.size();
    for(int i = 0; i < cmd_pool_size; i++){
        uint256_t cmd_hash = cmd_pool.front();
        if (decided_cmds.find(cmd_hash) == decided_cmds.end()){
            p_cmds.push_back(cmd_hash);
        }
        cmd_pool.pop();
        if (p_cmds.size() >= blk_size){ 
            break;
        }
    }

    for (const auto &_: parents) tails.erase(_);
    /* create the new block */
    block_t bnew = storage->add_blk(
        new Block(parents, p_cmds,
            hqc.second->clone(), std::move(extra),
            parents[0]->height + 1,
            hqc.first,
            nullptr
        ));
    const uint256_t bnew_hash = bnew->get_hash();
    on_deliver_blk(bnew);
    Proposal prop(id, current_view, bnew, nullptr);
    LOG_PROTO("propose %s", std::string(*bnew).c_str());
    /* self-vote */
    if (bnew->height <= vheight)
        throw std::runtime_error("new block should be higher than vheight");
    vheight = bnew->height;
    on_propose_(prop);
    /* boradcast to other replicas */
    do_broadcast_proposal(prop);
    const int vote_view = current_view;
    Vote vote(id, current_view, bnew_hash,
            create_part_cert(*priv_key, bnew_hash, vote_view, 1), this);
    do_vote(id, vote);
    on_receive_vote(vote);     
    SVote svote(id, current_view, bnew_hash,
            create_part_cert(*priv_key, bnew_hash, current_view, 1), this);
    do_svote(id, svote);
    on_receive_svote(svote);        
    return bnew;
}

void HotStuffCore::on_receive_proposal(const Proposal &prop) {
    LOG_PROTO("got %s", std::string(prop).c_str());
    if ( vote_timers.find(prop.view) != vote_timers.end() ) {
        stop_vote_timer(prop.view);
    }
    proposed_blks[prop.blk->get_hash()] = true;
    block_t bnew = prop.blk;
    sanity_check_delivered(bnew);
    bool opinion = (bnew->qc_ref->certified_view >= locking_view); 
    

    LOG_PROTO("now state: %s", std::string(*this).c_str());
    on_receive_proposal_(prop);
    if (opinion && !vote_disabled) {
        do_vote(prop.proposer,
            Vote(id, current_view, bnew->get_hash(),
                create_part_cert(*priv_key, bnew->get_hash(), current_view, 0), this));
        set_vote_timer(prop.view, prop.blk->get_hash(), prop.proposer, delta);
    }
}

void HotStuffCore::on_receive_vote(const Vote &vote) {
    LOG_PROTO("got %s", std::string(vote).c_str());
    LOG_PROTO("now state: %s", std::string(*this).c_str());
    block_t blk = get_delivered_blk(vote.blk_hash);
    assert(vote.cert);
    if (blk->certified) return;
    size_t qsize = blk->voted[vote.view].size();
    if (!blk->voted[vote.view].insert(vote.voter).second)
    {
        LOG_WARN("duplicate vote for %s from %d", get_hex10(vote.blk_hash).c_str(), vote.voter);
        return;
    }
    auto &qc = blk->self_certs[vote.view][0];
    if (qc == nullptr)
    {
        LOG_WARN("vote for block not proposed by itself");
        qc = create_quorum_cert(blk->get_hash(), vote.view, 0);
    }

    qc->add_part(vote.voter, *vote.cert);
    if (qsize + 1 == config.nmajority_opt)
    {
        qc->compute();
        blk->self_qc = qc->clone();
        update_hqc(blk, qc);
        on_qc_finish(blk);
        do_broadcast_qc(qc);
        blk->certified_view = vote.view;
        blk->certified = true;

        if (blk->certified_view >= current_view) {

            if (!fallback_lock)
                locking_view = blk->certified_view;
            if (!fallback_status) {
                update(blk);
                current_view = blk->certified_view + 1;
                on_enter_view_(current_view);
                enter_view(current_view);
            }
        }    
    }
}

void HotStuffCore::on_receive_svote(const SVote &vote) {
    LOG_PROTO("got %s", std::string(vote).c_str());
    LOG_PROTO("now state: %s", std::string(*this).c_str());
    block_t blk = get_delivered_blk(vote.blk_hash);
    assert(vote.cert);
    if (blk->certified) return;
    size_t qsize = blk->svoted[vote.view].size();
    if (!blk->svoted[vote.view].insert(vote.voter).second)
    {
        LOG_WARN("duplicate vote for %s from %d", get_hex10(vote.blk_hash).c_str(), vote.voter);
        return;
    }
    auto &qc = blk->self_certs[vote.view][1];
    if (qc == nullptr)
    {
        LOG_WARN("vote for block not proposed by itself");
        qc = create_quorum_cert(blk->get_hash(), vote.view, 1);
    }
    qc->add_part(vote.voter, *vote.cert);
    if (qsize + 1 == config.nmajority)
    {
        qc->compute();
        blk->self_qc = qc->clone();
        update_hqc(blk, qc);
        on_qc_finish(blk);
        do_broadcast_qc(qc);
        blk->certified_view = vote.view;
        blk->certified = true;

        if (blk->certified_view >= current_view) {
            if (!fallback_lock)
                locking_view = blk->certified_view;
            if (!fallback_status) {
                update(blk);
                current_view = blk->certified_view + 1;
                on_enter_view_(current_view);
                enter_view(current_view);
            }
        }
    
    }
}

void HotStuffCore::on_receive_blame(const Blame &blame) {
    size_t q_size = blamed[blame.view].size();
    if (q_size >= config.nmajority) return;
    if (q_size == 0)
        blame_certs[blame.view] = create_quorum_cert(blame.view_hash, blame.view, 2);
    if (!blamed[blame.view].insert(blame.blamer).second)
    {
        LOG_WARN("duplicate blame for view %d from %d", blame.view, blame.blamer);
        return;
    }
    blame_certs[blame.view]->add_part(blame.blamer, *blame.cert);
    if (q_size + 1 == config.nmajority) 
    {
        blame_certs[blame.view]->compute();

        if (blame.view >= current_view) {
            fallback_status = true;
            double t_sec = ((blame.view % config.nreplicas == id) ? 4*delta : 2*delta);
            set_fallback_status_timer(blame.view, t_sec);
        }
    }
}

void HotStuffCore::on_receive_qc(const quorum_cert_bt &qc) {
    uint256_t blk_hash = qc->get_obj_hash();    
    block_t blk = get_delivered_blk(blk_hash);
    if (blk->certified) return;
    update_hqc(blk, qc);
    on_qc_finish(blk);
    do_broadcast_qc(qc);
    blk->certified_view = qc->get_view();
    blk->certified = true;

    if (blk->certified_view >= current_view) {

        if (!fallback_lock)
            locking_view = blk->certified_view;
        if (!fallback_status) {
            update(blk);
            current_view = blk->certified_view + 1;
            on_enter_view_(current_view);
            enter_view(current_view);
        }
    }

}

void HotStuffCore::on_vote_timeout(int view, uint256_t blk_hash, ReplicaID proposer) {
    if (current_view == view) {
        do_svote(proposer,
            SVote(id, view, blk_hash,
                create_part_cert(*priv_key, blk_hash, view, 1), this));    
    }
}

void HotStuffCore::on_blame_timeout(int view) {
    if (current_view == view) {
        do_blame(Blame(id, current_view, Blame::get_view_hash(current_view),
            create_part_cert(*priv_key, Blame::get_view_hash(current_view), current_view, 2), this));
    }
}

void HotStuffCore::on_fallback_status_timeout(int view) {
    if (current_view <= view) {
        fallback_lock = true;
        double t_sec = ((view % config.nreplicas == id) ? 0 : delta);
        set_fallback_lock_timer(view, t_sec);
    }
}
void HotStuffCore::on_fallback_lock_timeout(int view) {
    if (current_view <= view) {
        fallback_status = false;
        fallback_lock = false;
        current_view = view + 1;
        on_enter_view_(current_view);
        enter_view(current_view);        
    }
}

/*** end HotStuff protocol logic ***/
void HotStuffCore::on_init(uint32_t nfaulty, uint32_t nfaulty_opt) {
    config.nmajority = config.nreplicas - nfaulty;
    config.nmajority_opt = config.nreplicas - nfaulty_opt;
    b0->qc = create_quorum_cert(b0->get_hash(), 0, 0);
    b0->qc->compute();
    b0->self_qc = b0->qc->clone();
    b0->qc_ref = b0;
    hqc = std::make_pair(b0, b0->qc->clone());
}

void HotStuffCore::prune(uint32_t staleness) {
    block_t start;
    /* skip the blocks */
    for (start = b_exec; staleness; staleness--, start = start->parents[0])
        if (!start->parents.size()) return;
    std::stack<block_t> s;
    start->qc_ref = nullptr;
    s.push(start);
    while (!s.empty())
    {
        auto &blk = s.top();
        if (blk->parents.empty())
        {
            storage->try_release_blk(blk);
            s.pop();
            continue;
        }
        blk->qc_ref = nullptr;
        s.push(blk->parents.back());
        blk->parents.pop_back();
    }
}

void HotStuffCore::add_replica(ReplicaID rid, const PeerId &peer_id,
                                pubkey_bt &&pub_key) {
    config.add_replica(rid,
            ReplicaInfo(rid, peer_id, std::move(pub_key)));
    b0->voted[0].insert(rid);
}

promise_t HotStuffCore::async_qc_finish(const block_t &blk) {
    if (blk->certified)
        return promise_t([](promise_t &pm) {
            pm.resolve();
        });
    auto it = qc_waiting.find(blk);
    if (it == qc_waiting.end())
        it = qc_waiting.insert(std::make_pair(blk, promise_t())).first;
    return it->second;
}

void HotStuffCore::on_qc_finish(const block_t &blk) {
    auto it = qc_waiting.find(blk);
    if (it != qc_waiting.end())
    {
        it->second.resolve();
        qc_waiting.erase(it);
    }
}

promise_t HotStuffCore::async_wait_proposal() {
    return propose_waiting.then([](const Proposal &prop) {
        return prop;
    });
}

promise_t HotStuffCore::async_wait_receive_proposal() {
    return receive_proposal_waiting.then([](const Proposal &prop) {
        return prop;
    });
}

promise_t HotStuffCore::async_hqc_update() {
    return hqc_update_waiting.then([this]() {
        return hqc.first;
    });
}

promise_t HotStuffCore::async_wait_enter_view(int view) {
    if (view <= 1) {
        view_waitings[view].resolve();
    }
    return view_waitings[view];
}

void HotStuffCore::on_propose_(const Proposal &prop) {
    auto t = std::move(propose_waiting);
    propose_waiting = promise_t();
    t.resolve(prop);
}

void HotStuffCore::on_receive_proposal_(const Proposal &prop) {
    auto t = std::move(receive_proposal_waiting);
    receive_proposal_waiting = promise_t();
    t.resolve(prop);
}

void HotStuffCore::on_enter_view_(const int view) {
    view_waitings[view].resolve();
}

void HotStuffCore::on_hqc_update() {
    auto t = std::move(hqc_update_waiting);
    hqc_update_waiting = promise_t();
    t.resolve();
}

HotStuffCore::operator std::string () const {
    DataStream s;
    s << "<hotstuff "
      << "hqc=" << get_hex10(hqc.first->get_hash()) << " "
      << "hqc.height=" << std::to_string(hqc.first->height) << " "
      << "b_lock=" << get_hex10(b_lock->get_hash()) << " "
      << "b_exec=" << get_hex10(b_exec->get_hash()) << " "
      << "vheight=" << std::to_string(vheight) << " "
      << "tails=" << std::to_string(tails.size()) << ">";
    return s;
}

}
