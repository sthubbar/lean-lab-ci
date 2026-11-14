import mpmath as mp
mp.mp.dps = 30
k = 1
n = 0
while True:
    z = mp.zetazero(k)
    if mp.im(z) > 100:
        break
    n += 1
    k += 1
print('zeros with gamma <= 100:', n, 'two-sided:', 2*n, '(repo comment says 58)')
