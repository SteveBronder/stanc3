
import numpy as np__
import tensorflow as tf__
import tensorflow_probability as tfp__
tfd__ = tfp__.distributions
tfb__ = tfp__.bijectors
from tensorflow.python.ops.parallel_for import pfor as pfor__

class test_cont_unbounded_model(tfd__.Distribution):

  def __init__(self):
    pass
     
  
  def log_prob_one_chain(self, params):
    target = 0
    
    p_normal = tf__.cast(params[0], tf__.float64)
    p_cauchy = tf__.cast(params[1], tf__.float64)
    p_gumbel = tf__.cast(params[2], tf__.float64)
    p_student_t = tf__.cast(params[3], tf__.float64)
    p_double_exponential = tf__.cast(params[4], tf__.float64)
    target += tf__.reduce_sum(tfd__.Normal((-tf__.cast(1, tf__.float64)),
                                           tf__.cast(5, tf__.float64)).log_prob(p_normal))
    target += tf__.reduce_sum(tfd__.Cauchy((-tf__.cast(3, tf__.float64)),
                                           tf__.cast(2, tf__.float64)).log_prob(p_cauchy))
    target += tf__.reduce_sum(tfd__.Gumbel(tf__.cast(3, tf__.float64),
                                           tf__.cast(1, tf__.float64)).log_prob(p_gumbel))
    target += tf__.reduce_sum(tfd__.StudentT(tf__.cast(2, tf__.float64),
                                             (-tf__.cast(1, tf__.float64)),
                                             tf__.cast(3, tf__.float64)).log_prob(p_student_t))
    target += tf__.reduce_sum(tfd__.Laplace(tf__.cast(0, tf__.float64),
                                            tf__.cast(3, tf__.float64)).log_prob(p_double_exponential))
    return target
     
  def log_prob(self, params):
    return tf__.vectorized_map(self.log_prob_one_chain, params)
    
     
  def parameter_shapes(self, nchains__):
    
    return [(nchains__, ), (nchains__, ), (nchains__, ), (nchains__, 
            ), (nchains__, )]
     
  def parameter_bijectors(self):
    
    return [tfb__.Identity(), tfb__.Identity(), tfb__.Identity(),
            tfb__.Identity(), tfb__.Identity()]
     
  def parameter_names(self):
    return ["p_normal", "p_cauchy", "p_gumbel", "p_student_t",
            "p_double_exponential"]
     
model = test_cont_unbounded_model