/* -*- C -*- */

/* Copyright 2023--2026 Nikita Danilov <danilov@gmail.com> */
/* See https://github.com/nikitadanilov/t2/blob/master/LICENCE for licencing information. */

#include <map>
#include <mutex>
#include <string>
#include <string.h>

extern "C" {
#include "bn.h"
}

static std::map<std::string, std::string> *map(struct kvbenchmark *kv) {
	return static_cast<std::map<std::string, std::string> *>(kv->u.m.m);
}

static std::mutex *lock(struct kvbenchmark *kv) {
	return static_cast<std::mutex *>(kv->u.m.l);
}

static void m_mount(struct benchmark *b) {
	b->kv.u.m.m = new std::map<std::string, std::string>;
	b->kv.u.m.l = new std::mutex;
}

static void m_umount(struct benchmark *b) {
	delete map(&b->kv);
	delete lock(&b->kv);
}

static void m_worker_init(struct rthread *rt, struct kvdata *d, int maxkey, int maxval) {
}

static void m_worker_fini(struct rthread *rt, struct kvdata *d) {
}

static int m_lookup(struct rthread *rt, struct kvdata *d, void *key, void *kcopy, int ksize, void *val, int vsize) {
	std::lock_guard<std::mutex> guard(*lock(d->b));
	auto m = map(d->b);
	auto it = m->find(std::string((const char *)key, ksize));
	if (it != m->end()) {
		std::string v = it->second;
		if ((int)v.length() <= vsize) {
			memcpy(val, v.c_str(), v.length());
			return 0;
		} else {
			return -ENAMETOOLONG;
		}
	} else {
		return -ENOENT;
	}
}

static int  m_insert(struct rthread *rt, struct kvdata *d, void *key, void *kcopy, int ksize, void *val, int vsize) {
	std::lock_guard<std::mutex> guard(*lock(d->b));
	return map(d->b)->insert({std::string((const char *)key, ksize), std::string((const char *)val, vsize)}).second ? 0 : -EEXIST;
}

static int  m_delete(struct rthread *rt, struct kvdata *d, void *key, void *kcopy, int ksize) {
	std::lock_guard<std::mutex> guard(*lock(d->b));
	return map(d->b)->erase(std::string((const char *)key, ksize)) > 0 ? 0 : -ENOENT;
}

static int  m_next(struct rthread *rt, struct kvdata *d, void *key, int ksize, enum t2_dir dir, int nr) {
	return 0;
}

extern "C" {
struct kv mapkv = {
	.mount       = &m_mount,
	.umount      = &m_umount,
	.worker_init = &m_worker_init,
	.worker_fini = &m_worker_fini,
	.lookup      = &m_lookup,
	.insert      = &m_insert,
	.del         = &m_delete,
	.next        = &m_next
};
}
