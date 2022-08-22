

include "utils/util.dfy"

module Main {

    import Util /* utils/util.dfy */

    datatype FileTypes = Cfg | Conf | Log | Txt


    function testAdd() : (res: int)
        ensures res == 5
    {
        Util.sum(2, 3)
    }

    function testMul() : (res: int)
        ensures res == 20
    {
        Util.prod(Util.prod(2, 5), 2)
    }

}