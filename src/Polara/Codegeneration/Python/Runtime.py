import math

# https://github.com/tpn/cuda-samples/blob/master/v9.0/4_Finance/BlackScholes/BlackScholes_gold.cpp
def normCdf (d: float):
    A1 =  0.31938153
    A2 = -0.356563782
    A3 =  1.781477937
    A4 = -1.821255978
    A5 =  1.330274429
    RSQRT2PI =  0.39894228040143267793994605993438
    K = 1.0 / (1.0 + 0.2316419 * abs(d))
    cnd = RSQRT2PI * math.exp (- 0.5 * d * d) * (K * (A1 + K * (A2 + K * (A3 + K * (A4 + K * A5)))))
    if d > 0:
        return 1.0 - cnd
    else:
        return cnd

def idx2int(a: int): 
    return a

def let(x, y):
    return y

def fold(f, l, n):
    res = n
    for i in l:
        res = f(i)(res)
    return res

#############################################################  
## Codegeneration to Python
#############################################################
