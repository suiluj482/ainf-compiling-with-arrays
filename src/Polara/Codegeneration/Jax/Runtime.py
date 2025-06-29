import jax.numpy as jnp
import jax
from jax import jit
from jax import lax

def normCdf(d):
    return jax.scipy.stats.norm.cdf(d)

def idx2int(a): 
    return a

def let(x, y):
    return y

def to_py(x):
    if isinstance(x, jnp.ndarray):
        return x.tolist()
    if isinstance(x, tuple):
        return tuple(to_py(i) for i in x)
    return x