#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "kissdb.h"

#define PASS() printf("  PASS\n")
#define FAIL(msg) do { printf("  FAIL: %s\n", msg); failures++; } while(0)

static int failures = 0;

/* mirrors test_db: kissdb_empty 16 2 2
   hash_table_size=16, key_size=2, value_size=2 */
#define HT_SIZE 16
#define KEY_SIZE 2
#define VAL_SIZE 2

/* mirrors collision_db: kissdb_empty 1 2 2 */
#define COLLISION_HT_SIZE 1

/* Simple 2-byte keys and values matching Rocq definitions */
static uint8_t k1[2] = {1, 0};
static uint8_t k2[2] = {2, 0};
static uint8_t k3[2] = {3, 0};
static uint8_t v1[2] = {10, 11};
static uint8_t v2[2] = {20, 21};
static uint8_t v3[2] = {30, 31};

static void open_fresh(KISSDB *db, const char *path, unsigned long ht_size) {
    if (KISSDB_open(db, path, KISSDB_OPEN_MODE_RWREPLACE, ht_size, KEY_SIZE, VAL_SIZE)) {
        printf("KISSDB_open failed for %s\n", path);
        exit(1);
    }
}

/* ===== Basic get/put tests ===== */

static void test_empty_get(void) {
    printf("test_empty_get...\n");
    KISSDB db;
    open_fresh(&db, "test_empty.db", HT_SIZE);
    uint8_t buf[VAL_SIZE];
    int r = KISSDB_get(&db, k1, buf);
    if (r == 1) PASS();
    else FAIL("expected not found");
    KISSDB_close(&db);
}

static void test_put_get_1(void) {
    printf("test_put_get_1...\n");
    KISSDB db;
    open_fresh(&db, "test_put_get_1.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v1, VAL_SIZE) == 0) PASS();
    else FAIL("wrong value");
    KISSDB_close(&db);
}

static void test_put_get_miss(void) {
    printf("test_put_get_miss...\n");
    KISSDB db;
    open_fresh(&db, "test_put_get_miss.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    uint8_t buf[VAL_SIZE];
    int r = KISSDB_get(&db, k2, buf);
    if (r == 1) PASS();
    else FAIL("expected not found");
    KISSDB_close(&db);
}

static void test_two_keys(void) {
    printf("test_two_keys...\n");
    KISSDB db;
    open_fresh(&db, "test_two_keys.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v1, VAL_SIZE) != 0) { FAIL("k1 wrong value"); goto done; }
    KISSDB_get(&db, k2, buf);
    if (memcmp(buf, v2, VAL_SIZE) != 0) { FAIL("k2 wrong value"); goto done; }
    PASS();
done:
    KISSDB_close(&db);
}

static void test_three_keys(void) {
    printf("test_three_keys...\n");
    KISSDB db;
    open_fresh(&db, "test_three_keys.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_put(&db, k3, v3);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v1, VAL_SIZE) != 0) { FAIL("k1 wrong value"); goto done; }
    KISSDB_get(&db, k2, buf);
    if (memcmp(buf, v2, VAL_SIZE) != 0) { FAIL("k2 wrong value"); goto done; }
    KISSDB_get(&db, k3, buf);
    if (memcmp(buf, v3, VAL_SIZE) != 0) { FAIL("k3 wrong value"); goto done; }
    PASS();
done:
    KISSDB_close(&db);
}

/* ===== Overwrite tests ===== */

static void test_overwrite(void) {
    printf("test_overwrite...\n");
    KISSDB db;
    open_fresh(&db, "test_overwrite.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k1, v2);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v2, VAL_SIZE) == 0) PASS();
    else FAIL("expected v2 after overwrite");
    KISSDB_close(&db);
}

static void test_overwrite_no_side_effect(void) {
    printf("test_overwrite_no_side_effect...\n");
    KISSDB db;
    open_fresh(&db, "test_overwrite_side.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_put(&db, k1, v3);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k2, buf);
    if (memcmp(buf, v2, VAL_SIZE) == 0) PASS();
    else FAIL("k2 was affected by overwrite of k1");
    KISSDB_close(&db);
}

static void test_double_overwrite(void) {
    printf("test_double_overwrite...\n");
    KISSDB db;
    open_fresh(&db, "test_double_overwrite.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k1, v2);
    KISSDB_put(&db, k1, v3);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v3, VAL_SIZE) == 0) PASS();
    else FAIL("expected v3 after double overwrite");
    KISSDB_close(&db);
}

/* ===== Structural tests ===== */

static void test_entry_count_0(void) {
    printf("test_entry_count_0...\n");
    /* empty db has no entries — verify via iterator */
    KISSDB db;
    open_fresh(&db, "test_count0.db", HT_SIZE);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 0) PASS();
    else FAIL("expected 0 entries");
    KISSDB_close(&db);
}

static void test_entry_count_1(void) {
    printf("test_entry_count_1...\n");
    KISSDB db;
    open_fresh(&db, "test_count1.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 1) PASS();
    else FAIL("expected 1 entry");
    KISSDB_close(&db);
}

static void test_entry_count_2(void) {
    printf("test_entry_count_2...\n");
    KISSDB db;
    open_fresh(&db, "test_count2.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 2) PASS();
    else FAIL("expected 2 entries");
    KISSDB_close(&db);
}

static void test_overwrite_no_grow(void) {
    printf("test_overwrite_no_grow...\n");
    KISSDB db;
    open_fresh(&db, "test_no_grow.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k1, v2);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 1) PASS();
    else FAIL("overwrite grew entry count");
    KISSDB_close(&db);
}

/* ===== Iterator tests ===== */

static void test_iter_empty(void) {
    printf("test_iter_empty...\n");
    KISSDB db;
    open_fresh(&db, "test_iter_empty.db", HT_SIZE);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    if (KISSDB_Iterator_next(&dbi, kb, vb) == 0) PASS();
    else FAIL("expected empty iterator");
    KISSDB_close(&db);
}

static void test_iter_one(void) {
    printf("test_iter_one...\n");
    KISSDB db;
    open_fresh(&db, "test_iter_one.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 1) PASS();
    else FAIL("expected 1 entry in iterator");
    KISSDB_close(&db);
}

static void test_iter_three(void) {
    printf("test_iter_three...\n");
    KISSDB db;
    open_fresh(&db, "test_iter_three.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_put(&db, k3, v3);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 3) PASS();
    else FAIL("expected 3 entries in iterator");
    KISSDB_close(&db);
}

static void test_iter_overwrite_count(void) {
    printf("test_iter_overwrite_count...\n");
    KISSDB db;
    open_fresh(&db, "test_iter_overwrite.db", HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k1, v2);
    KISSDB_Iterator dbi;
    KISSDB_Iterator_init(&db, &dbi);
    uint8_t kb[KEY_SIZE], vb[VAL_SIZE];
    int count = 0;
    while (KISSDB_Iterator_next(&dbi, kb, vb) > 0) count++;
    if (count == 1) PASS();
    else FAIL("overwrite should not duplicate in iterator");
    KISSDB_close(&db);
}

/* ===== Collision tests ===== */

static void test_collision_coexist(void) {
    printf("test_collision_coexist...\n");
    KISSDB db;
    open_fresh(&db, "test_collision.db", COLLISION_HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_put(&db, k3, v3);
    uint8_t buf[VAL_SIZE];
    KISSDB_get(&db, k1, buf);
    if (memcmp(buf, v1, VAL_SIZE) != 0) { FAIL("k1 wrong after collision"); goto done; }
    KISSDB_get(&db, k2, buf);
    if (memcmp(buf, v2, VAL_SIZE) != 0) { FAIL("k2 wrong after collision"); goto done; }
    KISSDB_get(&db, k3, buf);
    if (memcmp(buf, v3, VAL_SIZE) != 0) { FAIL("k3 wrong after collision"); goto done; }
    PASS();
done:
    KISSDB_close(&db);
}

static void test_collision_chains(void) {
    printf("test_collision_chains...\n");
    KISSDB db;
    open_fresh(&db, "test_collision_chains.db", COLLISION_HT_SIZE);
    KISSDB_put(&db, k1, v1);
    KISSDB_put(&db, k2, v2);
    KISSDB_put(&db, k3, v3);
    /* With ht_size=1, all 3 keys collide so we expect 3 hash tables */
    if (db.num_hash_tables == 3) PASS();
    else FAIL("expected 3 hash tables from chaining");
    KISSDB_close(&db);
}

static void cleanup(void) {
    remove("test_empty.db");
    remove("test_put_get_1.db");
    remove("test_put_get_miss.db");
    remove("test_two_keys.db");
    remove("test_three_keys.db");
    remove("test_overwrite.db");
    remove("test_overwrite_side.db");
    remove("test_double_overwrite.db");
    remove("test_count0.db");
    remove("test_count1.db");
    remove("test_count2.db");
    remove("test_no_grow.db");
    remove("test_iter_empty.db");
    remove("test_iter_one.db");
    remove("test_iter_three.db");
    remove("test_iter_overwrite.db");
    remove("test_collision.db");
    remove("test_collision_chains.db");
}

int main(void) {
    printf("=== KISSDB Rocq-mirrored tests ===\n\n");

    test_empty_get();
    test_put_get_1();
    test_put_get_miss();
    test_two_keys();
    test_three_keys();

    test_overwrite();
    test_overwrite_no_side_effect();
    test_double_overwrite();

    test_entry_count_0();
    test_entry_count_1();
    test_entry_count_2();
    test_overwrite_no_grow();

    test_iter_empty();
    test_iter_one();
    test_iter_three();
    test_iter_overwrite_count();

    test_collision_coexist();
    test_collision_chains();

    cleanup();
    printf("\n=== %d failure(s) ===\n", failures);
    return failures > 0 ? 1 : 0;
}