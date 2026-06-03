from sage.all import *

from theta.theta_structures.dimension_one import montgomery_curve_to_theta_null_point, theta_null_point_to_montgomery_curve
import params


def theta_isogeny(null_point):
    a0, a1 = null_point
    a0sq = a0*a0
    a1sq = a1*a1

    x0, x1 = a0sq + a1sq, a0sq - a1sq
    y0 = x0.sqrt()
    y1 = x1.sqrt()
    b0, b1 = y0 + y1, y0 - y1
    
    #Scaling to avoid factor
    b0 /= 2
    b1 /= 2

    return (b0, b1)

if __name__=="__main__":
    # Cleanup
    try:
        os.remove('zk_radical.txt')
    except:
        pass
    # Parameters setup
    p = params.set_params(0)

    # Set randomness
    rr = randint(1, 10000)
    set_random_seed(rr)
    print(f'{rr = }')

    # Start...
    Fp2, i = GF(p**2, name="i", modulus=[1, 0, 1]).objgen()
    E0 = EllipticCurve(Fp2, [1, 0])

    Theta0 = montgomery_curve_to_theta_null_point(E0)
    Thetai = Theta0
    zk_radical = 'A_is = ['
    for i, _ in enumerate(range(256)):
        Thetai = theta_isogeny(Thetai)
        zk_radical += f'{Thetai}, '
    zk_radical = zk_radical[:-2] + ']'
    EA = theta_null_point_to_montgomery_curve(Thetai)
    #assert EA.is_supersingular()
    with open('zk_radical.txt', 'a') as fh:
        fh.write(zk_radical + '\n')





