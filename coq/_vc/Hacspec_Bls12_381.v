(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t × fp_t × bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t × fp2_t × bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_1323 : fp_t) : fp2_t :=
  (n_1323, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_1324 : fp2_t) : fp2_t :=
  let '(n1_1325, n2_1326) :=
    n_1324 in 
  ((nat_mod_zero ) -% (n1_1325), (nat_mod_zero ) -% (n2_1326)).

Definition fp2add (n_1327 : fp2_t) (m_1328 : fp2_t) : fp2_t :=
  let '(n1_1329, n2_1330) :=
    n_1327 in 
  let '(m1_1331, m2_1332) :=
    m_1328 in 
  ((n1_1329) +% (m1_1331), (n2_1330) +% (m2_1332)).

Definition fp2sub (n_1333 : fp2_t) (m_1334 : fp2_t) : fp2_t :=
  fp2add (n_1333) (fp2neg (m_1334)).

Definition fp2mul (n_1335 : fp2_t) (m_1336 : fp2_t) : fp2_t :=
  let '(n1_1337, n2_1338) :=
    n_1335 in 
  let '(m1_1339, m2_1340) :=
    m_1336 in 
  let x1_1341 : fp_t :=
    ((n1_1337) *% (m1_1339)) -% ((n2_1338) *% (m2_1340)) in 
  let x2_1342 : fp_t :=
    ((n1_1337) *% (m2_1340)) +% ((n2_1338) *% (m1_1339)) in 
  (x1_1341, x2_1342).

Definition fp2inv (n_1343 : fp2_t) : fp2_t :=
  let '(n1_1344, n2_1345) :=
    n_1343 in 
  let t0_1346 : fp_t :=
    ((n1_1344) *% (n1_1344)) +% ((n2_1345) *% (n2_1345)) in 
  let t1_1347 : fp_t :=
    nat_mod_inv (t0_1346) in 
  let x1_1348 : fp_t :=
    (n1_1344) *% (t1_1347) in 
  let x2_1349 : fp_t :=
    (nat_mod_zero ) -% ((n2_1345) *% (t1_1347)) in 
  (x1_1348, x2_1349).

Definition fp2conjugate (n_1350 : fp2_t) : fp2_t :=
  let '(n1_1351, n2_1352) :=
    n_1350 in 
  (n1_1351, (nat_mod_zero ) -% (n2_1352)).

Definition fp6fromfp2 (n_1353 : fp2_t) : fp6_t :=
  (n_1353, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_1354 : fp6_t) : fp6_t :=
  let '(n1_1355, n2_1356, n3_1357) :=
    n_1354 in 
  (
    fp2sub (fp2zero ) (n1_1355),
    fp2sub (fp2zero ) (n2_1356),
    fp2sub (fp2zero ) (n3_1357)
  ).

Definition fp6add (n_1358 : fp6_t) (m_1359 : fp6_t) : fp6_t :=
  let '(n1_1360, n2_1361, n3_1362) :=
    n_1358 in 
  let '(m1_1363, m2_1364, m3_1365) :=
    m_1359 in 
  (
    fp2add (n1_1360) (m1_1363),
    fp2add (n2_1361) (m2_1364),
    fp2add (n3_1362) (m3_1365)
  ).

Definition fp6sub (n_1366 : fp6_t) (m_1367 : fp6_t) : fp6_t :=
  fp6add (n_1366) (fp6neg (m_1367)).

Definition fp6mul (n_1368 : fp6_t) (m_1369 : fp6_t) : fp6_t :=
  let '(n1_1370, n2_1371, n3_1372) :=
    n_1368 in 
  let '(m1_1373, m2_1374, m3_1375) :=
    m_1369 in 
  let eps_1376 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1377 : (fp_t × fp_t) :=
    fp2mul (n1_1370) (m1_1373) in 
  let t2_1378 : (fp_t × fp_t) :=
    fp2mul (n2_1371) (m2_1374) in 
  let t3_1379 : (fp_t × fp_t) :=
    fp2mul (n3_1372) (m3_1375) in 
  let t4_1380 : (fp_t × fp_t) :=
    fp2mul (fp2add (n2_1371) (n3_1372)) (fp2add (m2_1374) (m3_1375)) in 
  let t5_1381 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1380) (t2_1378)) (t3_1379) in 
  let x_1382 : (fp_t × fp_t) :=
    fp2add (fp2mul (t5_1381) (eps_1376)) (t1_1377) in 
  let t4_1383 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1370) (n2_1371)) (fp2add (m1_1373) (m2_1374)) in 
  let t5_1384 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1383) (t1_1377)) (t2_1378) in 
  let y_1385 : (fp_t × fp_t) :=
    fp2add (t5_1384) (fp2mul (eps_1376) (t3_1379)) in 
  let t4_1386 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1370) (n3_1372)) (fp2add (m1_1373) (m3_1375)) in 
  let t5_1387 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1386) (t1_1377)) (t3_1379) in 
  let z_1388 : (fp_t × fp_t) :=
    fp2add (t5_1387) (t2_1378) in 
  (x_1382, y_1385, z_1388).

Definition fp6inv (n_1389 : fp6_t) : fp6_t :=
  let '(n1_1390, n2_1391, n3_1392) :=
    n_1389 in 
  let eps_1393 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1394 : (fp_t × fp_t) :=
    fp2mul (n1_1390) (n1_1390) in 
  let t2_1395 : (fp_t × fp_t) :=
    fp2mul (n2_1391) (n2_1391) in 
  let t3_1396 : (fp_t × fp_t) :=
    fp2mul (n3_1392) (n3_1392) in 
  let t4_1397 : (fp_t × fp_t) :=
    fp2mul (n1_1390) (n2_1391) in 
  let t5_1398 : (fp_t × fp_t) :=
    fp2mul (n1_1390) (n3_1392) in 
  let t6_1399 : (fp_t × fp_t) :=
    fp2mul (n2_1391) (n3_1392) in 
  let x0_1400 : (fp_t × fp_t) :=
    fp2sub (t1_1394) (fp2mul (eps_1393) (t6_1399)) in 
  let y0_1401 : (fp_t × fp_t) :=
    fp2sub (fp2mul (eps_1393) (t3_1396)) (t4_1397) in 
  let z0_1402 : (fp_t × fp_t) :=
    fp2sub (t2_1395) (t5_1398) in 
  let t0_1403 : (fp_t × fp_t) :=
    fp2mul (n1_1390) (x0_1400) in 
  let t0_1404 : (fp_t × fp_t) :=
    fp2add (t0_1403) (fp2mul (eps_1393) (fp2mul (n3_1392) (y0_1401))) in 
  let t0_1405 : (fp_t × fp_t) :=
    fp2add (t0_1404) (fp2mul (eps_1393) (fp2mul (n2_1391) (z0_1402))) in 
  let t0_1406 : (fp_t × fp_t) :=
    fp2inv (t0_1405) in 
  let x_1407 : (fp_t × fp_t) :=
    fp2mul (x0_1400) (t0_1406) in 
  let y_1408 : (fp_t × fp_t) :=
    fp2mul (y0_1401) (t0_1406) in 
  let z_1409 : (fp_t × fp_t) :=
    fp2mul (z0_1402) (t0_1406) in 
  (x_1407, y_1408, z_1409).

Definition fp12fromfp6 (n_1410 : fp6_t) : fp12_t :=
  (n_1410, fp6zero ).

Definition fp12neg (n_1411 : fp12_t) : fp12_t :=
  let '(n1_1412, n2_1413) :=
    n_1411 in 
  (fp6sub (fp6zero ) (n1_1412), fp6sub (fp6zero ) (n2_1413)).

Definition fp12add (n_1414 : fp12_t) (m_1415 : fp12_t) : fp12_t :=
  let '(n1_1416, n2_1417) :=
    n_1414 in 
  let '(m1_1418, m2_1419) :=
    m_1415 in 
  (fp6add (n1_1416) (m1_1418), fp6add (n2_1417) (m2_1419)).

Definition fp12sub (n_1420 : fp12_t) (m_1421 : fp12_t) : fp12_t :=
  fp12add (n_1420) (fp12neg (m_1421)).

Definition fp12mul (n_1422 : fp12_t) (m_1423 : fp12_t) : fp12_t :=
  let '(n1_1424, n2_1425) :=
    n_1422 in 
  let '(m1_1426, m2_1427) :=
    m_1423 in 
  let gamma_1428 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1429 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1424) (m1_1426) in 
  let t2_1430 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1425) (m2_1427) in 
  let x_1431 : (fp2_t × fp2_t × fp2_t) :=
    fp6add (t1_1429) (fp6mul (t2_1430) (gamma_1428)) in 
  let y_1432 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (fp6add (n1_1424) (n2_1425)) (fp6add (m1_1426) (m2_1427)) in 
  let y_1433 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (fp6sub (y_1432) (t1_1429)) (t2_1430) in 
  (x_1431, y_1433).

Definition fp12inv (n_1434 : fp12_t) : fp12_t :=
  let '(n1_1435, n2_1436) :=
    n_1434 in 
  let gamma_1437 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1438 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1435) (n1_1435) in 
  let t2_1439 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1436) (n2_1436) in 
  let t1_1440 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (t1_1438) (fp6mul (gamma_1437) (t2_1439)) in 
  let t2_1441 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (t1_1440) in 
  let x_1442 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1435) (t2_1441) in 
  let y_1443 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (fp6mul (n2_1436) (t2_1441)) in 
  (x_1442, y_1443).

Definition fp12exp (n_1444 : fp12_t) (k_1445 : scalar_t) : fp12_t :=
  let c_1446 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_1446 :=
    foldi (usize 0) (usize 256) (fun i_1447 c_1446 =>
      let c_1446 :=
        fp12mul (c_1446) (c_1446) in 
      let '(c_1446) :=
        if nat_mod_bit (k_1445) ((usize 255) - (i_1447)):bool then (
          let c_1446 :=
            fp12mul (c_1446) (n_1444) in 
          (c_1446)) else ((c_1446)) in 
      (c_1446))
    c_1446 in 
  c_1446.

Definition fp12conjugate (n_1448 : fp12_t) : fp12_t :=
  let '(n1_1449, n2_1450) :=
    n_1448 in 
  (n1_1449, fp6neg (n2_1450)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_1451 : g1_t) (q_1452 : g1_t) : g1_t :=
  let '(x1_1453, y1_1454, _) :=
    p_1451 in 
  let '(x2_1455, y2_1456, _) :=
    q_1452 in 
  let x_diff_1457 : fp_t :=
    (x2_1455) -% (x1_1453) in 
  let y_diff_1458 : fp_t :=
    (y2_1456) -% (y1_1454) in 
  let xovery_1459 : fp_t :=
    (y_diff_1458) *% (nat_mod_inv (x_diff_1457)) in 
  let x3_1460 : fp_t :=
    ((nat_mod_exp (xovery_1459) (@repr WORDSIZE32 2)) -% (x1_1453)) -% (
      x2_1455) in 
  let y3_1461 : fp_t :=
    ((xovery_1459) *% ((x1_1453) -% (x3_1460))) -% (y1_1454) in 
  (x3_1460, y3_1461, false).

Definition g1double_a (p_1462 : g1_t) : g1_t :=
  let '(x1_1463, y1_1464, _) :=
    p_1462 in 
  let x12_1465 : fp_t :=
    nat_mod_exp (x1_1463) (@repr WORDSIZE32 2) in 
  let xovery_1466 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_1465)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_1464))) in 
  let x3_1467 : fp_t :=
    (nat_mod_exp (xovery_1466) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_1463)) in 
  let y3_1468 : fp_t :=
    ((xovery_1466) *% ((x1_1463) -% (x3_1467))) -% (y1_1464) in 
  (x3_1467, y3_1468, false).

Definition g1double (p_1469 : g1_t) : g1_t :=
  let '(x1_1470, y1_1471, inf1_1472) :=
    p_1469 in 
  (if (((y1_1471) !=.? (nat_mod_zero )) && (negb (inf1_1472))):bool then (
      g1double_a (p_1469)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_1473 : g1_t) (q_1474 : g1_t) : g1_t :=
  let '(x1_1475, y1_1476, inf1_1477) :=
    p_1473 in 
  let '(x2_1478, y2_1479, inf2_1480) :=
    q_1474 in 
  (if (inf1_1477):bool then (q_1474) else ((if (inf2_1480):bool then (
          p_1473) else ((if ((p_1473) =.? (q_1474)):bool then (g1double (
                p_1473)) else ((if (negb (((x1_1475) =.? (x2_1478)) && ((
                        y1_1476) =.? ((nat_mod_zero ) -% (
                          y2_1479))))):bool then (g1add_a (p_1473) (
                    q_1474)) else ((nat_mod_zero , nat_mod_zero , true))))))))).

Definition g1mul (m_1481 : scalar_t) (p_1482 : g1_t) : g1_t :=
  let t_1483 : (fp_t × fp_t × bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_1483 :=
    foldi (usize 0) (usize 256) (fun i_1484 t_1483 =>
      let t_1483 :=
        g1double (t_1483) in 
      let '(t_1483) :=
        if nat_mod_bit (m_1481) ((usize 255) - (i_1484)):bool then (
          let t_1483 :=
            g1add (t_1483) (p_1482) in 
          (t_1483)) else ((t_1483)) in 
      (t_1483))
    t_1483 in 
  t_1483.

Definition g1neg (p_1485 : g1_t) : g1_t :=
  let '(x_1486, y_1487, inf_1488) :=
    p_1485 in 
  (x_1486, (nat_mod_zero ) -% (y_1487), inf_1488).

Definition g2add_a (p_1489 : g2_t) (q_1490 : g2_t) : g2_t :=
  let '(x1_1491, y1_1492, _) :=
    p_1489 in 
  let '(x2_1493, y2_1494, _) :=
    q_1490 in 
  let x_diff_1495 : (fp_t × fp_t) :=
    fp2sub (x2_1493) (x1_1491) in 
  let y_diff_1496 : (fp_t × fp_t) :=
    fp2sub (y2_1494) (y1_1492) in 
  let xovery_1497 : (fp_t × fp_t) :=
    fp2mul (y_diff_1496) (fp2inv (x_diff_1495)) in 
  let t1_1498 : (fp_t × fp_t) :=
    fp2mul (xovery_1497) (xovery_1497) in 
  let t2_1499 : (fp_t × fp_t) :=
    fp2sub (t1_1498) (x1_1491) in 
  let x3_1500 : (fp_t × fp_t) :=
    fp2sub (t2_1499) (x2_1493) in 
  let t1_1501 : (fp_t × fp_t) :=
    fp2sub (x1_1491) (x3_1500) in 
  let t2_1502 : (fp_t × fp_t) :=
    fp2mul (xovery_1497) (t1_1501) in 
  let y3_1503 : (fp_t × fp_t) :=
    fp2sub (t2_1502) (y1_1492) in 
  (x3_1500, y3_1503, false).

Definition g2double_a (p_1504 : g2_t) : g2_t :=
  let '(x1_1505, y1_1506, _) :=
    p_1504 in 
  let x12_1507 : (fp_t × fp_t) :=
    fp2mul (x1_1505) (x1_1505) in 
  let t1_1508 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_1507) in 
  let t2_1509 : (fp_t × fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_1506)) in 
  let xovery_1510 : (fp_t × fp_t) :=
    fp2mul (t1_1508) (t2_1509) in 
  let t1_1511 : (fp_t × fp_t) :=
    fp2mul (xovery_1510) (xovery_1510) in 
  let t2_1512 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_1505) in 
  let x3_1513 : (fp_t × fp_t) :=
    fp2sub (t1_1511) (t2_1512) in 
  let t1_1514 : (fp_t × fp_t) :=
    fp2sub (x1_1505) (x3_1513) in 
  let t2_1515 : (fp_t × fp_t) :=
    fp2mul (xovery_1510) (t1_1514) in 
  let y3_1516 : (fp_t × fp_t) :=
    fp2sub (t2_1515) (y1_1506) in 
  (x3_1513, y3_1516, false).

Definition g2double (p_1517 : g2_t) : g2_t :=
  let '(x1_1518, y1_1519, inf1_1520) :=
    p_1517 in 
  (if (((y1_1519) !=.? (fp2zero )) && (negb (inf1_1520))):bool then (
      g2double_a (p_1517)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_1521 : g2_t) (q_1522 : g2_t) : g2_t :=
  let '(x1_1523, y1_1524, inf1_1525) :=
    p_1521 in 
  let '(x2_1526, y2_1527, inf2_1528) :=
    q_1522 in 
  (if (inf1_1525):bool then (q_1522) else ((if (inf2_1528):bool then (
          p_1521) else ((if ((p_1521) =.? (q_1522)):bool then (g2double (
                p_1521)) else ((if (negb (((x1_1523) =.? (x2_1526)) && ((
                        y1_1524) =.? (fp2neg (y2_1527))))):bool then (g2add_a (
                    p_1521) (q_1522)) else ((fp2zero , fp2zero , true))))))))).

Definition g2mul (m_1529 : scalar_t) (p_1530 : g2_t) : g2_t :=
  let t_1531 : (fp2_t × fp2_t × bool) :=
    (fp2zero , fp2zero , true) in 
  let t_1531 :=
    foldi (usize 0) (usize 256) (fun i_1532 t_1531 =>
      let t_1531 :=
        g2double (t_1531) in 
      let '(t_1531) :=
        if nat_mod_bit (m_1529) ((usize 255) - (i_1532)):bool then (
          let t_1531 :=
            g2add (t_1531) (p_1530) in 
          (t_1531)) else ((t_1531)) in 
      (t_1531))
    t_1531 in 
  t_1531.

Definition g2neg (p_1533 : g2_t) : g2_t :=
  let '(x_1534, y_1535, inf_1536) :=
    p_1533 in 
  (x_1534, fp2neg (y_1535), inf_1536).

Definition twist (p_1537 : g1_t) : (fp12_t × fp12_t) :=
  let '(p0_1538, p1_1539, _) :=
    p_1537 in 
  let x_1540 : ((fp2_t × fp2_t × fp2_t) × fp6_t) :=
    ((fp2zero , fp2fromfp (p0_1538), fp2zero ), fp6zero ) in 
  let y_1541 : (fp6_t × (fp2_t × fp2_t × fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_1539), fp2zero )) in 
  (x_1540, y_1541).

Definition line_double_p (r_1542 : g2_t) (p_1543 : g1_t) : fp12_t :=
  let '(r0_1544, r1_1545, _) :=
    r_1542 in 
  let a_1546 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_1544) (r0_1544)) in 
  let a_1547 : (fp_t × fp_t) :=
    fp2mul (a_1546) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_1545))) in 
  let b_1548 : (fp_t × fp_t) :=
    fp2sub (r1_1545) (fp2mul (a_1547) (r0_1544)) in 
  let a_1549 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1547)) in 
  let b_1550 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1548)) in 
  let '(x_1551, y_1552) :=
    twist (p_1543) in 
  fp12neg (fp12sub (fp12sub (y_1552) (fp12mul (a_1549) (x_1551))) (b_1550)).

Definition line_add_p
  (r_1553 : g2_t)
  (q_1554 : g2_t)
  (p_1555 : g1_t)
  : fp12_t :=
  let '(r0_1556, r1_1557, _) :=
    r_1553 in 
  let '(q0_1558, q1_1559, _) :=
    q_1554 in 
  let a_1560 : (fp_t × fp_t) :=
    fp2mul (fp2sub (q1_1559) (r1_1557)) (fp2inv (fp2sub (q0_1558) (
          r0_1556))) in 
  let b_1561 : (fp_t × fp_t) :=
    fp2sub (r1_1557) (fp2mul (a_1560) (r0_1556)) in 
  let a_1562 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1560)) in 
  let b_1563 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1561)) in 
  let '(x_1564, y_1565) :=
    twist (p_1555) in 
  fp12neg (fp12sub (fp12sub (y_1565) (fp12mul (a_1562) (x_1564))) (b_1563)).

Definition frobenius (f_1566 : fp12_t) : fp12_t :=
  let '((g0_1567, g1_1568, g2_1569), (h0_1570, h1_1571, h2_1572)) :=
    f_1566 in 
  let t1_1573 : (fp_t × fp_t) :=
    fp2conjugate (g0_1567) in 
  let t2_1574 : (fp_t × fp_t) :=
    fp2conjugate (h0_1570) in 
  let t3_1575 : (fp_t × fp_t) :=
    fp2conjugate (g1_1568) in 
  let t4_1576 : (fp_t × fp_t) :=
    fp2conjugate (h1_1571) in 
  let t5_1577 : (fp_t × fp_t) :=
    fp2conjugate (g2_1569) in 
  let t6_1578 : (fp_t × fp_t) :=
    fp2conjugate (h2_1572) in 
  let c1_1579 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_1580 : seq uint8 :=
    array_to_le_bytes (c1_1579) in 
  let c1_1581 : fp_t :=
    nat_mod_from_byte_seq_le (c1_1580) : fp_t in 
  let c2_1582 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_1583 : seq uint8 :=
    array_to_le_bytes (c2_1582) in 
  let c2_1584 : fp_t :=
    nat_mod_from_byte_seq_le (c2_1583) : fp_t in 
  let gamma11_1585 : (fp_t × fp_t) :=
    (c1_1581, c2_1584) in 
  let gamma12_1586 : (fp_t × fp_t) :=
    fp2mul (gamma11_1585) (gamma11_1585) in 
  let gamma13_1587 : (fp_t × fp_t) :=
    fp2mul (gamma12_1586) (gamma11_1585) in 
  let gamma14_1588 : (fp_t × fp_t) :=
    fp2mul (gamma13_1587) (gamma11_1585) in 
  let gamma15_1589 : (fp_t × fp_t) :=
    fp2mul (gamma14_1588) (gamma11_1585) in 
  let t2_1590 : (fp_t × fp_t) :=
    fp2mul (t2_1574) (gamma11_1585) in 
  let t3_1591 : (fp_t × fp_t) :=
    fp2mul (t3_1575) (gamma12_1586) in 
  let t4_1592 : (fp_t × fp_t) :=
    fp2mul (t4_1576) (gamma13_1587) in 
  let t5_1593 : (fp_t × fp_t) :=
    fp2mul (t5_1577) (gamma14_1588) in 
  let t6_1594 : (fp_t × fp_t) :=
    fp2mul (t6_1578) (gamma15_1589) in 
  ((t1_1573, t3_1591, t5_1593), (t2_1590, t4_1592, t6_1594)).

Definition final_exponentiation (f_1595 : fp12_t) : fp12_t :=
  let fp6_1596 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1595) in 
  let finv_1597 : (fp6_t × fp6_t) :=
    fp12inv (f_1595) in 
  let fp6_1_1598 : (fp6_t × fp6_t) :=
    fp12mul (fp6_1596) (finv_1597) in 
  let fp8_1599 : (fp6_t × fp6_t) :=
    frobenius (frobenius (fp6_1_1598)) in 
  let f_1600 : (fp6_t × fp6_t) :=
    fp12mul (fp8_1599) (fp6_1_1598) in 
  let u_1601 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let u_half_1602 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 7566188111470821376) : scalar_t in 
  let t0_1603 : (fp6_t × fp6_t) :=
    fp12mul (f_1600) (f_1600) in 
  let t1_1604 : (fp6_t × fp6_t) :=
    fp12exp (t0_1603) (u_1601) in 
  let t1_1605 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1604) in 
  let t2_1606 : (fp6_t × fp6_t) :=
    fp12exp (t1_1605) (u_half_1602) in 
  let t2_1607 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1606) in 
  let t3_1608 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1600) in 
  let t1_1609 : (fp6_t × fp6_t) :=
    fp12mul (t3_1608) (t1_1605) in 
  let t1_1610 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1609) in 
  let t1_1611 : (fp6_t × fp6_t) :=
    fp12mul (t1_1610) (t2_1607) in 
  let t2_1612 : (fp6_t × fp6_t) :=
    fp12exp (t1_1611) (u_1601) in 
  let t2_1613 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1612) in 
  let t3_1614 : (fp6_t × fp6_t) :=
    fp12exp (t2_1613) (u_1601) in 
  let t3_1615 : (fp6_t × fp6_t) :=
    fp12conjugate (t3_1614) in 
  let t1_1616 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1611) in 
  let t3_1617 : (fp6_t × fp6_t) :=
    fp12mul (t1_1616) (t3_1615) in 
  let t1_1618 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1616) in 
  let t1_1619 : (fp6_t × fp6_t) :=
    frobenius (frobenius (frobenius (t1_1618))) in 
  let t2_1620 : (fp6_t × fp6_t) :=
    frobenius (frobenius (t2_1613)) in 
  let t1_1621 : (fp6_t × fp6_t) :=
    fp12mul (t1_1619) (t2_1620) in 
  let t2_1622 : (fp6_t × fp6_t) :=
    fp12exp (t3_1617) (u_1601) in 
  let t2_1623 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1622) in 
  let t2_1624 : (fp6_t × fp6_t) :=
    fp12mul (t2_1623) (t0_1603) in 
  let t2_1625 : (fp6_t × fp6_t) :=
    fp12mul (t2_1624) (f_1600) in 
  let t1_1626 : (fp6_t × fp6_t) :=
    fp12mul (t1_1621) (t2_1625) in 
  let t2_1627 : (fp6_t × fp6_t) :=
    frobenius (t3_1617) in 
  let t1_1628 : (fp6_t × fp6_t) :=
    fp12mul (t1_1626) (t2_1627) in 
  t1_1628.

Definition pairing (p_1629 : g1_t) (q_1630 : g2_t) : fp12_t :=
  let t_1631 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_1632 : (fp2_t × fp2_t × bool) :=
    q_1630 in 
  let f_1633 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_1632, f_1633) :=
    foldi (usize 1) (usize 64) (fun i_1634 '(r_1632, f_1633) =>
      let lrr_1635 : (fp6_t × fp6_t) :=
        line_double_p (r_1632) (p_1629) in 
      let r_1632 :=
        g2double (r_1632) in 
      let f_1633 :=
        fp12mul (fp12mul (f_1633) (f_1633)) (lrr_1635) in 
      let '(r_1632, f_1633) :=
        if nat_mod_bit (t_1631) (((usize 64) - (i_1634)) - (
            usize 1)):bool then (let lrq_1636 : (fp6_t × fp6_t) :=
            line_add_p (r_1632) (q_1630) (p_1629) in 
          let r_1632 :=
            g2add (r_1632) (q_1630) in 
          let f_1633 :=
            fp12mul (f_1633) (lrq_1636) in 
          (r_1632, f_1633)) else ((r_1632, f_1633)) in 
      (r_1632, f_1633))
    (r_1632, f_1633) in 
  final_exponentiation (fp12conjugate (f_1633)).

Definition test_fp2_prop_add_neg (a_1637 : fp2_t) : bool :=
  let b_1638 : (fp_t × fp_t) :=
    fp2neg (a_1637) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_1637) (b_1638)).
QuickChick (forAll g_fp2_t (fun a_1637 : fp2_t =>test_fp2_prop_add_neg a_1637)).


Definition test_fp2_prop_mul_inv (a_1639 : fp2_t) : bool :=
  let b_1640 : (fp_t × fp_t) :=
    fp2inv (a_1639) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_1639) (b_1640)).
QuickChick (forAll g_fp2_t (fun a_1639 : fp2_t =>test_fp2_prop_mul_inv a_1639)).


Definition test_extraction_issue  : bool :=
  let b_1641 : (fp_t × fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_1641)).
QuickChick (test_extraction_issue).


Definition test_fp6_prop_mul_inv (a_1642 : fp6_t) : bool :=
  let b_1643 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (a_1642) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_1642) (b_1643)).
QuickChick (forAll g_fp6_t (fun a_1642 : fp6_t =>test_fp6_prop_mul_inv a_1642)).


Definition test_fp6_prop_add_neg (a_1644 : fp6_t) : bool :=
  let b_1645 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (a_1644) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_1644) (b_1645)).
QuickChick (forAll g_fp6_t (fun a_1644 : fp6_t =>test_fp6_prop_add_neg a_1644)).


Definition test_fp12_prop_add_neg (a_1646 : fp12_t) : bool :=
  let b_1647 : (fp6_t × fp6_t) :=
    fp12neg (a_1646) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_1646) (
      b_1647)).
QuickChick (
  forAll g_fp12_t (fun a_1646 : fp12_t =>test_fp12_prop_add_neg a_1646)).


Definition test_fp12_prop_mul_inv (a_1648 : fp12_t) : bool :=
  let b_1649 : (fp6_t × fp6_t) :=
    fp12inv (a_1648) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_1648) (
      b_1649)).
QuickChick (
  forAll g_fp12_t (fun a_1648 : fp12_t =>test_fp12_prop_mul_inv a_1648)).


