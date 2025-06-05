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