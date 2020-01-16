import numpy as np

def prim_symmetric_geometric(a, b):
    """
    :param a: the center of the geometric distribution, can be an ndarray
    :param b: the alpha parameter to the symmetric geometric distribution

    :return: a sample/ndarray of samples from the given geometric distribution
    """
    import numpy as np
    shape = np.shape(a)
    if shape == (1,) or shape == ():
        np.random.seed()
        x = np.random.geometric(1 - b)
        np.random.seed()
        y = np.random.geometric(1 - b)
        return a + x - y
    else:
        noise = np.zeros(shape=np.shape(a))
        for index, value in np.ndenumerate(noise):
            np.random.seed()
            x = np.random.geometric(1 - b)
            np.random.seed()
            y = np.random.geometric(1 - b)
            noise[index] = x - y
        return a + noise

def loop_geometric(true_answer_sens_eps):
  """
  :param true_answer_sens_eps: an array-like of (true_answer, (sensitivity, epsilon))
  :return: a list of (noised_answer, variance)
  """
  loop_acc = (true_answer_sens_eps, [])
  loop_cond = not [] == loop_acc[0]
  while loop_cond:
    if loop_acc[0]:
      uncons_head = loop_acc[0][0]
      uncons_tail = (loop_acc[0])[1:]
      uncons_result = (uncons_head, uncons_tail)
    else:
      uncons_result = None
    if loop_acc[0]:
      uncons_head1 = loop_acc[0][0]
      uncons_tail1 = (loop_acc[0])[1:]
      uncons_result1 = (uncons_head1, uncons_tail1)
    else:
      uncons_result1 = None
    if loop_acc[0]:
      uncons_head2 = loop_acc[0][0]
      uncons_tail2 = (loop_acc[0])[1:]
      uncons_result2 = (uncons_head2, uncons_tail2)
    else:
      uncons_result2 = None
    x = (prim_symmetric_geometric(uncons_result[0][0], (np.exp((0.0 - uncons_result1[0][1][1]) / uncons_result2[0][1][0]))))
    if loop_acc[0]:
      uncons_head3 = loop_acc[0][0]
      uncons_tail3 = (loop_acc[0])[1:]
      uncons_result3 = (uncons_head3, uncons_tail3)
    else:
      uncons_result3 = None
    if loop_acc[0]:
      uncons_head4 = loop_acc[0][0]
      uncons_tail4 = (loop_acc[0])[1:]
      uncons_result4 = (uncons_head4, uncons_tail4)
    else:
      uncons_result4 = None
    if loop_acc[0]:
      uncons_head5 = loop_acc[0][0]
      uncons_tail5 = (loop_acc[0])[1:]
      uncons_result5 = (uncons_head5, uncons_tail5)
    else:
      uncons_result5 = None
    if loop_acc[0]:
      uncons_head6 = loop_acc[0][0]
      uncons_tail6 = (loop_acc[0])[1:]
      uncons_result6 = (uncons_head6, uncons_tail6)
    else:
      uncons_result6 = None
    if loop_acc[0]:
      uncons_head7 = loop_acc[0][0]
      uncons_tail7 = (loop_acc[0])[1:]
      uncons_result7 = (uncons_head7, uncons_tail7)
    else:
      uncons_result7 = None
    if loop_acc[0]:
      uncons_head8 = loop_acc[0][0]
      uncons_tail8 = (loop_acc[0])[1:]
      uncons_result8 = (uncons_head8, uncons_tail8)
    else:
      uncons_result8 = None
    if loop_acc[0]:
      uncons_head9 = loop_acc[0][0]
      uncons_tail9 = (loop_acc[0])[1:]
      uncons_result9 = (uncons_head9, uncons_tail9)
    else:
      uncons_result9 = None
    loop_acc = (uncons_result3[1], loop_acc[1] + [(x, 2.0 * (np.exp((0.0 - uncons_result4[0][1][1]) / uncons_result5[0][1][0])) / ((1.0 - (np.exp((0.0 - uncons_result6[0][1][1]) / uncons_result7[0][1][0]))) * (1.0 - (np.exp((0.0 - uncons_result8[0][1][1]) / uncons_result9[0][1][0])))))])
    loop_cond = not [] == loop_acc[0]
  x1 = loop_acc
  return x1[1]

print(loop_geometric([[1, [2, 3]],
                      [2, [2, 3]],
                     ]))
