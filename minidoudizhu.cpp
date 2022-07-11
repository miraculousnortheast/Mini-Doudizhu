#include <vector>
#include <string>
#include <ctime>
#include <cstdlib>
#include <algorithm>
#include <iostream>
#include <cmath>
#include <queue>
#include "jsoncpp/json.h" // 在平台上，C++编译时默认包含此库
#define LOCAL_DEBUG

using namespace std;
namespace doudizhu
{
    // 游戏使用的牌总数，不要修改
    const int MAX_CARD_NUM = 54;

    // 游戏使用的牌类型的数目，不要修改
    const int MAX_CARD_TYPE_NUM = 15;

    // 对每种牌的数目编码，每种占4bit
    typedef unsigned long long EncodedCards;
    const EncodedCards NO_CARDS = 0ull;
    const EncodedCards FULL_CARDS = 0x114444444000000ull;

    // bitmap，用于枚举子集
    typedef unsigned long long Bitmap;
    const Bitmap EMPTY_SET = 0ull;

    // 牌张按照3-JOKER的顺序从0-53编号
    typedef int Card;

    // 定义牌张类型：一共15种不同大小的牌
    typedef enum
    {
        THREE = 0,
        FOUR = 1,
        FIVE = 2,
        SIX = 3,
        SEVEN = 4,
        EIGHT = 5,
        NINE = 6,
        TEN = 7,
        JACK = 8,
        QUEEN = 9,
        KING = 10,
        ACE = 11,
        TWO = 12,
        Joker = 13,
        JOKER = 14
    } CardType;

    // 游戏中最小的牌张类型（可修改为NINE，适配迷你斗地主）
    const CardType START_CARD = NINE;

    // 主牌类型
    // 对于连牌 (456789:SINGLE; 334455:PAIR; JJJQQQ:TRIPLET, 77778888:QUADRUPLE)
    // 对于含副牌的 (333A:TRIPLET; 222255JJ:QUADRUPLE)
    // 对于连牌含副牌的 (34KKKAAA:TRIPLET; 4444555589JQ:QUADRUPLE)
    typedef enum
    {
        PASS = 0,      // 过
        SINGLE = 1,    // 单张
        PAIR = 2,      // 对子
        TRIPLET = 3,   // 三张
        QUADRUPLE = 4, // 四张
        ROCKET = 5     //火箭
    } MainCardComboType;

    // 某种主牌类型要想形成合法序列（顺子、连对、飞机、连炸），所需的最小长度
    const int SEQ_MIN_LENGTH[] = {0, 5, 3, 2, 2, 1};

    //全局记录当前轮数三位玩家的历史出牌记录
    int turn;
    vector<EncodedCards> history_combo[3];
    //全局记录当前轮数三位玩家需要压的牌型
    vector<vector<EncodedCards>> history_last_action(3, vector<EncodedCards>(0));
    //全局记录未知的另外两位玩家的手牌，
    vector<int> unknown_cards(MAX_CARD_TYPE_NUM);
    vector<int> full_cards(MAX_CARD_TYPE_NUM);
    vector<int> my_initial_cards_counter(MAX_CARD_TYPE_NUM);
    EncodedCards encoded_my_initial_cards;
    //另外两家已经出的牌，用于sample 函数中
    EncodedCards cards_played_a = 0, cards_played_b = 0, cards_played_c;
    // a 是下家, b 是上家
    int player_a, player_b;
    //后验分布的cdf
    vector<double> cumulative_probability;
    // player a 可能的手牌
    vector<EncodedCards> possible_hands_a;

    // 返回具体牌张的类型：（0-14编号，对应于THREE, FOUR,... Joker, JOKER）
    inline CardType cardTypeOf(Card c)
    {
        return CardType((c >> 2) + int(bool(c & 1) && (c >= MAX_CARD_NUM - 2))); // if c == 53, then the cardType is c/4 + 1.
    }

    // 将牌张序列转为各种牌的数目向量
    vector<int> toCardCountVector(const vector<Card> &card_combo)
    {
        vector<int> card_counter(MAX_CARD_TYPE_NUM);
        for (Card c : card_combo)
        {
            card_counter[cardTypeOf(c)]++;
        }
        return card_counter;
    }

    // 将各种牌的数目向量转为EncodedCards表示
    EncodedCards toEncodedCards(const vector<int> &card_counter)
    {
        EncodedCards combo = NO_CARDS;
        for (CardType i = START_CARD; i <= JOKER; i = CardType(i + 1))
        {
            // 4i~(4i+3)的位置上编码第i种牌的数目
            combo |= (EncodedCards(card_counter[i]) << (i << 2));
        }
        return combo;
    }

    //将EncodedCard转化为CardCounter
    vector<int> encodedCardsToCardCountVector(EncodedCards card_combo)
    {
        vector<int> card_counter(MAX_CARD_TYPE_NUM);
        for (CardType i = START_CARD; i <= JOKER; i = CardType(i + 1))
        {
            card_counter[i] = (card_combo >> (i << 2)) & 0xf;
        }
        return card_counter;
    }

    // 在EncodedCards combo中将CardType ct类型的牌的数目增加n
    inline EncodedCards addToEncodedCards(
        CardType ct, EncodedCards combo, int n = 1)
    {
        return combo + (EncodedCards(n) << (ct << 2));
    }

    // 在EncodedCards combo中将CardType ct类型的牌的数目减少n
    inline EncodedCards minusFromEncodedCards(
        CardType ct, EncodedCards combo, int n = 1)
    {
        return combo - (EncodedCards(n) << (ct << 2));
    }

    // 在EncodedCards中判断某种牌有多少张
    inline int numCardOfEncoded(
        CardType ct, EncodedCards combo)
    {
        return int((combo >> (ct << 2)) & 0xfull);
    }


    bool isFinished(const vector<EncodedCards> &state)
    {
        bool flag;
        for (EncodedCards cards: state)
        {
            vector<int> card_counter = encodedCardsToCardCountVector(cards);
            flag = true;
            for (int i=0;i<card_counter.size();i++)
                if(card_counter[i])
                {
                    flag = false;
                    break;
                }
            if (flag)
                return true;
        }
        return false;
    }

    // 分析一手牌的类型、大小等
    struct Hand
    {
        // 一手牌的编码形式，每4位对应一种牌的数目。
        EncodedCards combo;
        // 一手牌主牌的类型：单张（顺）、两张（顺）……火箭
        MainCardComboType type;
        // 一手牌主牌开始的牌张
        CardType start;
        // 主牌的长度：单牌1，对牌1，顺子按其长度来
        int length;
        // 副牌不带、带单还是带双(0,1,2)
        int appendix;

        // 解析对手的一手牌（牌张编码、主牌类型、主牌开始、主牌长度、副牌所带数目）
        // card_counter表示这一手牌每种有多少张
        Hand(const vector<int> &card_counter)
        {
            // 初始化这一手牌的编码形式为空
            combo = NO_CARDS;
            // 最多的牌是哪一种（取最先出现的那一种）
            CardType max_freq_card = START_CARD;
            // 最多出现的牌出现了多少次
            int max_freq = 0;
            // 出现次数最多的牌有几种
            int max_freq_length = 0;
            // 最小出现的手牌是什么牌
            CardType min_card = JOKER;
            // 这一手牌一共有多少张
            int total_cards = 0;
            // 编码对手这一手牌到位图中
            combo = toEncodedCards(card_counter);
            // 扫一遍对手的牌，看看出现次数最多的牌、主牌的长度
            for (CardType i = START_CARD; i <= JOKER; i = CardType(i + 1))
            {
                total_cards += card_counter[i];
                // 记录出现次数最多的牌是哪一种，及其出现次数
                if (card_counter[i] > max_freq)
                {
                    max_freq = card_counter[i];
                    max_freq_card = i;
                    max_freq_length = 1;
                }
                else if (card_counter[i] == max_freq)
                {
                    max_freq_length++;
                }
                // 记录出现的最小牌张
                if (card_counter[i] != 0 && i < min_card)
                {
                    min_card = i;
                }
            }
            // 下面判断主要牌型
            // 空牌，PASS
            if (max_freq == 0)
            {
                type = PASS;
                start = START_CARD;
                length = 0;
                appendix = 0;
                return;
            }
            // 火箭
            if (min_card == Joker && total_cards == 2)
            {
                type = ROCKET;
                start = Joker;
                length = 2;
                appendix = 0;
                return;
            }
            // 序列牌（单、双、三、四：独立出现或者连续出现）
            type = MainCardComboType(max_freq);
            // 主牌开始的牌张
            start = max_freq_card;
            // 主牌长度
            length = max_freq_length;
            // 副牌带0,1,2张
            appendix = total_cards / length - int(type);
        }
        bool isPass()
        {
            return type == PASS;
        }
        bool isSingle()
        {
            return type == SINGLE && length == 1;
        }
        bool isPair()
        {
            return type == PAIR && length == 1;
        }
        bool isBomb()
        {
            return type == QUADRUPLE && length == 1 && appendix == 0;
        }
        bool isRocket()
        {
            return type == ROCKET;
        }

        // 判断是三带(0,1,2)还是四带(0,2,4)
        bool isTripletOrQuadruple()
        {
            return (type == TRIPLET || type == QUADRUPLE) && length == 1;
        }

        // 判断有无副牌
        bool hasAppendix()
        {
            return appendix > 0;
        }

        // 含有副牌的连续三带、四带也算Chain，但是长度至少得是2
        bool isChain()
        {
            return ((type == SINGLE && length >= SEQ_MIN_LENGTH[SINGLE]) || (type == PAIR && length >= SEQ_MIN_LENGTH[PAIR]) || (type == TRIPLET && length >= SEQ_MIN_LENGTH[TRIPLET]) || (type == QUADRUPLE && length >= SEQ_MIN_LENGTH[QUADRUPLE]));
        }
    };

    // Check if a card combo is PASS
    bool isPass(EncodedCards combo)
    {
        return Hand(encodedCardsToCardCountVector(combo)).isPass();
    }

    // 使用上一手牌、我方现有的牌，构造游戏状态。可分析我方可行动作
    struct DoudizhuState
    {
        // 轮到我出的时候，我有什么牌
        vector<Card> my_cards;
        // 我各种牌都有多少张
        vector<int> my_card_counter;
        // 上一手出了什么牌
        Hand last_action;

        // 传入我有的牌、对手上一次出的牌（0-53）编码
        DoudizhuState(vector<Card> mine, const vector<Card> &last) : my_cards(mine),
                                                                     my_card_counter(toCardCountVector(mine)),
                                                                     last_action(toCardCountVector(last)) {}
        // 只传入牌的编码和last action, 注意此时不能使用decodeAction 函数
        DoudizhuState(EncodedCards mine, EncodedCards last) : my_cards(),
                                                              my_card_counter(encodedCardsToCardCountVector(mine)),
                                                              last_action(encodedCardsToCardCountVector(last)) {}
        // 我的牌中是否有火箭，如果有，则返回该牌型的EncodedCards表示
        EncodedCards genRocket()
        {
            EncodedCards action = NO_CARDS;
            if (my_card_counter[Joker] == 1 && my_card_counter[JOKER] == 1)
            {
                action = addToEncodedCards(Joker, NO_CARDS, 1);
                action = addToEncodedCards(JOKER, action, 1);
            }
            return action;
        }

        // 返回我的牌中所有炸弹的列表，均用EncodedCards类型表示
        vector<EncodedCards> genBombs()
        {
            vector<EncodedCards> actions;
            EncodedCards action = NO_CARDS;
            for (CardType i = START_CARD; i <= TWO; i = CardType(i + 1))
            {
                if (my_card_counter[i] == 4)
                {
                    action = addToEncodedCards(i, NO_CARDS, 4);
                    actions.push_back(action);
                }
            }
            return actions;
        }

        // 下一手可以出什么牌，返回所有可能动作的列表，元素是EncodedCards的形式
        // generate_appendix == true: 生成的动作中包含三带单、对，四带两单、对的各种情况，包含带的副牌
        // generate_appendix == false: 只生成主牌（三带四带的连三连四部分），不含带的副牌，且主牌部分不重复
        vector<EncodedCards> validActions(bool generate_appendix = true)
        {
            // 待返回动作列表
            vector<EncodedCards> actions;
            // 用于临时保存同一手主牌对应的不同副牌选择
            vector<EncodedCards> appendix_actions;
            // 用于构造主牌动作
            EncodedCards action = NO_CARDS;
            // 用于构造副牌选择
            EncodedCards appendix_action = NO_CARDS;
            // 如果有火箭，生成火箭作为动作，否则为NO_CARDS
            EncodedCards rocket = genRocket();
            // 生成当前我方持有的炸弹列表
            vector<EncodedCards> bombs = genBombs();

            // 上家牌非Pass并且带副牌，生成动作才需考虑副牌，否则只考虑我方意愿
            generate_appendix = generate_appendix &&
                                (last_action.hasAppendix() || last_action.isPass());

            // 如果轮到我先出牌
            if (last_action.isPass())
            {
                // 生成单、对（范围从最小牌到大王）
                for (CardType i = START_CARD; i <= JOKER; i = CardType(i + 1))
                {
                    // j=1单/j=2对
                    for (int j = 1; j <= 2 && j <= my_card_counter[i]; ++j)
                    {
                        action = addToEncodedCards(i, NO_CARDS, j);
                        actions.push_back(action);
                    }
                }

                // 生成三带，四带（有副牌当且仅当generate_appendix，范围从最小牌到2）
                for (CardType i = START_CARD; i <= TWO; i = CardType(i + 1))
                {
                    // 如果牌有3张，考虑三带；如果有4张，三带、四带都要考虑
                    for (int j = 3, num_appendix; j <= my_card_counter[i]; ++j)
                    {
                        action = addToEncodedCards(i, NO_CARDS, j);
                        if (generate_appendix)
                        {
                            // 是三带1还是四带2
                            num_appendix = j == 3 ? 1 : 2;
                            // 带单牌还是双牌
                            for (int k = 1; k <= 2; ++k)
                            {
                                // 生成副牌
                                appendix_actions = generateAppendix(i, 1, num_appendix, k);
                                for (EncodedCards ec : appendix_actions)
                                {
                                    appendix_action = ec;
                                    // 副牌可以直接加到主牌动作上（位串设计保证了这一点）
                                    actions.push_back(action + appendix_action);
                                }
                            }
                            // 如果不生成副牌，这里不添加四张，因为后面添加了
                        }
                        else if (j < QUADRUPLE)
                        {
                            actions.push_back(action);
                        }
                    }
                }
                // accumulated_length[1,2,3,4]: 统计到某种牌时，记录以其为结尾的最长（单/对/三/四）连牌长度
                vector<int> accumulated_length(5);
                // 暂时保存action的值
                vector<EncodedCards> a(5);
                // 生成连续牌：连单、连双、连三（带）、连四（带）
                for (CardType i = START_CARD; i <= ACE; i = CardType(i + 1))
                {
                    // 考虑连续的单、双、三、四张牌
                    for (int j = 1; j <= my_card_counter[i]; ++j)
                    {
                        // 能进循环说明牌张数目够
                        accumulated_length[j]++;
                        // 将j张类型i的牌添加到a[j]中
                        a[j] = addToEncodedCards(i, a[j], j);
                    }
                    for (int j = my_card_counter[i] + 1; j <= 4; ++j)
                    {
                        // 进了这个循环说明牌张数目不够，清空连牌长度，连牌断裂
                        accumulated_length[j] = 0;
                        a[j] = NO_CARDS;
                    }
                    // 考虑连单、双、三、四的序列
                    for (int j = 1, num_appendixes; j <= 4; ++j)
                    {
                        // 当前序列以i结尾，开头位于i-accumulated_length[j]+1处
                        for (CardType k = CardType(i - accumulated_length[j] + 1);
                             // j重的牌序列最短长度要大于等于SEQ_MIN_LENGTH[j]，因此k最多到i-SEQ_MIN_LENGTH[j]+1
                             k <= i - SEQ_MIN_LENGTH[j] + 1; k = CardType(k + 1))
                        {
                            action = a[j];
                            if (generate_appendix && j >= 3)
                            {
                                // 如果j=3，那么需要为每段生成一份副牌，如果j=4，那么需要为每段生成2份副牌
                                num_appendixes = j == 3 ? 1 : 2;
                                // 副牌是带单牌还是对牌（l=1单，l=2对）
                                for (int l = 1; l <= 2; ++l)
                                {
                                    // 生成所有以牌种i为结尾，长度为i-k+1的连三/连四的副牌
                                    //（每段配num_appendixes份副牌，并且副牌张数为l(1/2)）
                                    appendix_actions = generateAppendix(i, i - k + 1, num_appendixes, l);
                                    for (EncodedCards ec : appendix_actions)
                                    {
                                        appendix_action = ec;
                                        actions.push_back(action + appendix_action);
                                    }
                                }
                            }
                            else
                            {
                                actions.push_back(action);
                            }
                            // 考虑过k开始到i-SEQ_MIN_LENGTH[j]+1的子序列后，考虑从k+1开始的子序列
                            a[j] = minusFromEncodedCards(k, a[j], j);
                        }
                    }
                }
                // 生成火箭、炸弹的情况在最后考虑了，这里不返回。
            }
            else {
                // You could always pass
                actions.push_back (0);
                if (last_action.isRocket())
                {
                    // 对面火箭，直接开摆，返回空动作集
                    return actions;
                }
                else if (last_action.isBomb())
                {
                    // 对面是炸弹，找更大的炸弹
                    for (EncodedCards ec : bombs)
                    {
                        // 炸弹比较只需要比较bitmap大小即可
                        if (ec > last_action.combo)
                        {
                            action = ec;
                            actions.push_back(action);
                        }
                    }
                    // 考虑火箭的情况
                    if (rocket != NO_CARDS)
                    {
                        actions.push_back(rocket);
                    }
                    // 直接返回，下面非炸弹的情况才需要考虑所有能打的炸弹
                    return actions;
                }
                else if (last_action.isSingle() || last_action.isPair())
                {
                    // 考虑对面出单牌、对牌的情况
                    for (CardType i = CardType(last_action.start + 1); i <= JOKER; i = CardType(i + 1))
                    {
                        // 如果我的牌够出，那么直接加入动作列表
                        if (my_card_counter[i] >= last_action.type)
                        {
                            action = addToEncodedCards(i, NO_CARDS, last_action.type);
                            actions.push_back(action);
                        }
                    }
                    // 生成炸弹火箭最后考虑了，这里不返回
                }
                else if (last_action.isTripletOrQuadruple())
                {
                    // 三带、四带等（不连）
                    for (CardType i = CardType(last_action.start + 1); i <= TWO; i = CardType(i + 1))
                    {
                        if (my_card_counter[i] >= last_action.type)
                        {
                            action = addToEncodedCards(i, NO_CARDS, last_action.type);
                            // 如果需要生成副牌，那么将其考虑到action中
                            if (generate_appendix)
                            {
                                appendix_actions = generateAppendix(i);
                                for (EncodedCards ec : appendix_actions)
                                {
                                    appendix_action = ec;
                                    actions.push_back(action + appendix_action);
                                }
                            }
                            else if (last_action.type < QUADRUPLE)
                            {
                                // 后面会添加炸弹，所以这里不重复添加，只加入三张
                                actions.push_back(action);
                            }
                        }
                    }
                    // 生成炸弹火箭的情况最后考虑了，这里不返回
                }
                else if (last_action.isChain())
                {
                    // 连续牌：可能为连单、双、三、四。对于连三、四还可能带副牌
                    // 当前找到的序列长度
                    int cur_length = 0;
    
                    // 从前一手牌最小牌张+1开始考虑，寻找连牌
                    for (CardType i = CardType(last_action.start + 1); i <= ACE; i = CardType(i + 1))
                    {
                        // 如果我拥有的此种牌张数目大于上一手序列的重复数
                        if (my_card_counter[i] >= last_action.type)
                        {
                            cur_length++;
                            action = addToEncodedCards(i, action, last_action.type);
                            // 如果当前发现的序列长度超过上一手序列的长度，将序列头部剪去
                            if (cur_length > last_action.length)
                            {
                                action = minusFromEncodedCards(
                                    CardType(i - last_action.length), action, last_action.type);
                            }
                            // 如果序列长度达标了，可以加入动作列表
                            if (cur_length >= last_action.length)
                            {
                                if (generate_appendix)
                                {
                                    appendix_actions = generateAppendix(i);
                                    for (EncodedCards ec : appendix_actions)
                                    {
                                        appendix_action = ec;
                                        actions.push_back(action + appendix_action);
                                    }
                                }
                                else
                                {
                                    actions.push_back(action);
                                }
                            }
                        }
                        else
                        {
                            cur_length = 0;
                            action = NO_CARDS;
                        }
                    }
                }
            }
            // 最后考虑炸弹的情况
            for (EncodedCards ec : bombs)
            {
                action = ec;
                actions.push_back(action);
            }
            // 最后考虑火箭的情况
            if (rocket != NO_CARDS)
            {
                actions.push_back(rocket);
            }
            return actions;
        }

        // 如果只传第一个参数意味着是针对对手的牌型反制，否则是在上一手Pass的情况下随意出牌
        // 参数分别为：我方主牌最大牌张、主牌序列长度、带牌数目（1单/对或2单/对）、带单(1)或双(2) -> 生成备选副牌列表
        vector<EncodedCards> generateAppendix(CardType end_type,
                                              int seq_length = 1, int num_appendixes = 1, int appendix_type = 1)
        {
            // 存储所有可能的副牌
            vector<EncodedCards> appendixes;
            EncodedCards appendix = NO_CARDS;
            // 依据上家出的牌是三带还是四带还是pass，如果pass则采用输入的参数
            if (last_action.type == TRIPLET)
            {
                // 三带主牌部分长度
                seq_length = last_action.length;
                // 三带副牌部分为1单或者1对
                num_appendixes = 1;
                // 三带副牌部分为单还是双
                appendix_type = last_action.appendix;
            }
            else if (last_action.type == QUADRUPLE)
            {
                // 四带主牌部分长度
                seq_length = last_action.length;
                // 四带副牌部分为2单或者2对
                num_appendixes = 2;
                // 四带副牌部分为单还是双
                appendix_type = last_action.appendix;
            }
            else if (last_action.isPass())
            {
                // 按照输入的seq_length来
                // 按照输入的num_appendixes来
                // 按照输入的appendix_type来
                // 所以这里不用写任何东西
            }
            // 有多少种副牌可以用
            int useable_appendix_count = 0;
            // 需要多少种副牌
            int all_appendix_needed = seq_length * num_appendixes;
            // 保存可用的副牌种类
            vector<CardType> useable_appendix_set;
            // 遍历我方手牌，看看那些种类的牌数目够做副牌
            for (CardType i = START_CARD; i <= JOKER; i = CardType(i + 1))
            {
                // 如果我有的牌大于副牌所需数目，并且当前的牌不在序列范围之内
                if (my_card_counter[i] >= appendix_type &&
                    (i > end_type || i <= end_type - seq_length))
                {
                    useable_appendix_count++;
                    // 标记该种牌可以用作副牌
                    useable_appendix_set.push_back(i);
                }
            }
            // 如果可用的副牌种类数目不够，返回空集
            if (useable_appendix_count < all_appendix_needed)
            {
                return appendixes;
            }

            // 临时保存副牌选择子集
            Bitmap appendix_subset = (1ull << all_appendix_needed) - 1ull;
            // 临时保存appendix_subset
            Bitmap s;
            // 副牌选择子集的范围
            Bitmap appendix_subset_limit = 1ull << useable_appendix_count;

            // Gosper's Hack Algorithm
            // 枚举C(usable_appendix_count, all_appendixes_needed)个可行的副牌选择子集
            Bitmap lb, r;
            while (appendix_subset < appendix_subset_limit)
            {
                s = appendix_subset;
                appendix = NO_CARDS;
                // 解析生成的子集，将之对应到牌的类别上
                for (int j = 0; s != EMPTY_SET; ++j)
                {
                    if (s & 1ull)
                    {
                        appendix = addToEncodedCards(useable_appendix_set[j], appendix, appendix_type);
                    }
                    s >>= 1;
                }
                appendixes.push_back(appendix);

                // 以下代码负责枚举子集，不用管这一部分
                lb = appendix_subset & -appendix_subset;
                r = appendix_subset + lb;
                appendix_subset = ((appendix_subset ^ r) >> (__builtin_ctzll(lb) + 2)) | r;
            }

            return appendixes;
        }

        // 对validAction生成的可能动作，解析出实际要出的牌张
        vector<Card> decodeAction(EncodedCards encoded_action)
        {
            vector<Card> action;
            CardType ct;
            int encoded_ct_num;
            // 对每一张我有的牌，看看我打算打出去的动作中需不需要这张牌
            for (Card c : my_cards)
            {
                ct = cardTypeOf(c);
                encoded_ct_num = numCardOfEncoded(ct, encoded_action);
                // 如果需要，就加入输出列表，并且在打出的动作中删掉一张这种牌
                if (encoded_ct_num > 0)
                {
                    encoded_action = minusFromEncodedCards(ct, encoded_action, 1);
                    action.push_back(c);
                }
            }
            return action;
        }
    };
    double evaluate_each_player(vector<int> card)
    // card是该玩家手里的牌，类似于mycardcounter
    {
        double value = 0;
        int triplet_num = 0;
        int hand_num = 0; //这些牌在理想情况下几手可以出完
        //评估每一个人的手牌的value value越大说明他的牌越好
        //有王炸
        if (card[Joker] == 1 && card[JOKER] == 1)
        {
            value += 130; //后期调参
            hand_num++;
        }
        else if (card[Joker] == 1)
        {
            value += 40;
            hand_num++;
        }
        else if (card[JOKER] == 1)
        {
            value += 48;
            hand_num++;
        }
        for (CardType i = START_CARD; i <= TWO; i = CardType(i + 1))
        {
            if (card[i] == 3) //有三带一/三带二 的可能性
            {
                triplet_num++;
                value += i * 6; // value与牌面的值有关 如i=NINE时 value=36 i=TWO时 value=72
                hand_num++;
            }
            if (card[i] == 4)
            {                        //如果有炸弹
                value += i * 7 + 30; // i=NINE时 value=72 i=TWO value=114
                hand_num++;
            }
        }
        for (CardType i = START_CARD; i <= TWO; i = CardType(i + 1))
        {
            //扫描单个的和一对的 如果可以和三带凑一起就凑一起
            if (card[i] == 1)
            {
                if (triplet_num)
                {
                    triplet_num--;
                }
                else
                {
                    value += i * 2; // TWO 24
                    hand_num++;
                }
            }
            if (card[i] == 2)
            {
                if (triplet_num)
                {
                    triplet_num--;
                }
                else
                {
                    value += i * 3; // TWO 36
                    hand_num++;
                }
            }
        }
        value -= hand_num * 10;
        return value;
    }

    //如果我们是农民，那么p1card是农民的牌
    //四个参数分别对应我们的牌，对手1的牌，对手2的牌，我们是不是地主
    double evaluate_global_situation(vector<int> my_card,
                                     vector<int> p1_card, vector<int> p2_card, int pos) //评估全局的当前局面的好坏
    {
        double global_value = 0;
        if (pos == 0)
        {
            //如果我们是地主
            global_value += evaluate_each_player(my_card) - 0.5 * (evaluate_each_player(p1_card) + (evaluate_each_player(p2_card)));
        }
        else
        {
            global_value += 0.5 * (evaluate_each_player(my_card) + evaluate_each_player(p1_card)) - evaluate_each_player(p2_card);
        }
        return global_value;
    }

    //估计给定combo在特定手牌和上家的情况下被打出的概率
    double getComboProbability(EncodedCards my_combo, doudizhu::DoudizhuState my_state)
    {
        //概率正比于打出去的牌的得分和余下手牌的得分
        vector<EncodedCards> valid_actions = my_state.validActions(true);
        //可以什么都不打，理论上应该排除地主第一轮不打牌，但应该没啥大问题
        valid_actions.push_back(0);
        EncodedCards encoded_my_cards = toEncodedCards(my_state.my_card_counter);
        // printf("my combo: %llx\n", my_combo>>24);
        //假设其他人按照正比于1/2^k的概率随机出牌，k是比my_combo分数高的出牌方案的个数
        double flag = -1, combo_score;
        int k = 0;
        combo_score = evaluate_each_player(encodedCardsToCardCountVector(my_combo)) + evaluate_each_player(encodedCardsToCardCountVector(encoded_my_cards - my_combo));
        for (EncodedCards combo : valid_actions)
        {
            // printf("valid action: %llx\n", combo>>24);
            if (combo == my_combo)
            {
                flag = 1;
            }
            else
            {
                double tmp = evaluate_each_player(encodedCardsToCardCountVector(combo)) + evaluate_each_player(encodedCardsToCardCountVector(encoded_my_cards - combo));
                if (tmp >= combo_score)
                    k++;
            }
        }
        if (flag == -1)
        {
            cout << "Error in function getComboProbability! The input combo is not valid!\n";
            return -1;
        }
        else
            return pow(0.95, k);
    }

    //给定未知的牌集合和已知的手牌，遍历所有可能的初始手牌，并记录在这个初始手牌情况下，history 记录的情况发生的条件概率
    void transverseAllHands(CardType cur, vector<int> &known_cards_a, vector<int> &known_cards_b)
    {
        static double normalizor_factor = 0;
        int cur_card_num_a = 0;
        for (int i = 0; i < MAX_CARD_TYPE_NUM; i++)
            cur_card_num_a += known_cards_a[i];
        int max_card_num = 9 + 3 * (!player_a);
        // printf("cur card %d, cur %d, max %d\n",cur, cur_card_num_a, max_card_num);
        //搜索到端点后，记录在此条件下，出现history 中的局面的未归一化的概率，之后按照此概率随机
        if (cur_card_num_a == max_card_num)
        {
            for (int i = START_CARD; i < MAX_CARD_TYPE_NUM; i++)
            {
                known_cards_b[i] = full_cards[i] - known_cards_a[i] - my_initial_cards_counter[i];
            }
            // printf("transverse to %llx %llx unknown: %llx\n", (toEncodedCards(known_cards_a))>>24, (toEncodedCards(known_cards_b))>>24, (toEncodedCards(unknown_cards))>>24);
            //  Duel!
            //这两个变量维护当前轮数时二者的手牌
            int pos = 3 - player_a - player_b;
            EncodedCards cur_cards_a = toEncodedCards(known_cards_a), cur_cards_b = toEncodedCards(known_cards_b);
            double conditional_probability = 1;
            //假设另外两人每一轮出牌都是独立的，计算在给定二者手牌时，他们按照真实的出牌方式出牌的条件概率
            for (int i = 0; i < turn; i++)
            {
                // turn 是玩家进行的局数，如果另一个player 在玩家顺序后面，那么他时比玩家少经历一轮的
                if (i != turn - 1 || player_a < pos)
                {
                    conditional_probability *= getComboProbability(history_combo[player_a][i], DoudizhuState(cur_cards_a, history_last_action[player_a][i]));
                    cur_cards_a -= history_combo[player_a][i];
                }
                else if (i != turn - 1 || player_b < pos)
                {
                    conditional_probability *= getComboProbability(history_combo[player_b][i], DoudizhuState(cur_cards_b, history_last_action[player_b][i]));
                    cur_cards_b -= history_combo[player_b][i];
                }
            }
            //计算在给定二者手牌时，他们按照真实的出牌方式出牌的条件概率的累计分布函数
            normalizor_factor += conditional_probability;
            cumulative_probability.push_back(normalizor_factor);
            possible_hands_a.push_back(toEncodedCards(known_cards_a));
            return;
        }
        if (cur > JOKER)
            return;
        for (int i = 0; i <= min(4 - known_cards_a[cur], unknown_cards[cur]); i++)
        {
            if (cur_card_num_a + i > max_card_num)
                break;
            known_cards_a[cur] += i;
            transverseAllHands(CardType(cur + 1), known_cards_a, known_cards_b);
            known_cards_a[cur] -= i;
        }
    }

    //从已经计算出的后验分布中采样,输出一个vector分别是自己的下家的当前手牌，自己的上家的当前手牌, 自己的当前手牌
    vector<EncodedCards> sample()
    {
        double random_number = (rand() % 100000000) / (double)100000000;
        int l = 0, r = possible_hands_a.size() - 1;
        while (l < r)
        {
            int mid = (l + r) / 2;
            if (cumulative_probability[mid] < random_number)
                l = mid + 1;
            else
                r = mid;
        }
        vector<EncodedCards> ans;
        ans.push_back(possible_hands_a[l] - cards_played_a);
        ans.push_back(FULL_CARDS - possible_hands_a[l] - encoded_my_initial_cards - cards_played_b);
        ans.push_back(encoded_my_initial_cards - cards_played_c);
        return ans;
    }

    /** play a card from previous hand */
    EncodedCards playCard (EncodedCards prev, EncodedCards combo)
    {
        for (int i = 0; i < MAX_CARD_TYPE_NUM; i++)
            prev = minusFromEncodedCards((CardType)i, prev, numCardOfEncoded((CardType)i, combo)); 
        return prev;
    }

    class MCTNode {
    public:
        MCTNode *parent;
        EncodedCards last_action;
        vector<pair<EncodedCards, MCTNode*> > childs; 
        double score;
        int curPlayer, dep, nEval;
        bool finishNode;
        MCTNode(EncodedCards _last_action, MCTNode * _parent = NULL, int _dep = 0):curPlayer(2), dep(_dep), nEval(0), score(0),
                            finishNode(false), parent(_parent)
        {
            if (isPass(_last_action) && _parent != NULL)
                if (!isPass(_parent->last_action))
                    _last_action = _parent->last_action;
            last_action = _last_action;
        }
        
    };

    double UCT (MCTNode * p, MCTNode * v)
    {
        return v->score / (double) v->nEval + sqrt(log((double) p->nEval)/(double) v->nEval);
    }

    pair<EncodedCards, MCTNode*> bestChild (MCTNode * v)
    {
        pair<EncodedCards, MCTNode*> bestPair = v->childs[0];
        double score = UCT (v, bestPair.second);
        for (auto p: v->childs)        
            if (UCT(v, p.second) > score)
            {
                bestPair = p;
                score = UCT(v, p.second);
            }
        return bestPair;
    }

    MCTNode* expand (MCTNode * v, vector<EncodedCards> & prev_state)
    {
        MCTNode * p;
        vector<int> vec;
        for (int i = 0; i < v->childs.size(); i++)
            vec.push_back(i);
        random_shuffle (vec.begin(), vec.end());
        for (int i = 0; i < v->childs.size(); i++)
            if (v->childs[vec[i]].second == NULL)
            {
                EncodedCards last_action = v->childs[vec[i]].first;
                p = v->childs[vec[i]].second = new MCTNode (last_action, v, v->dep+1);
                p->curPlayer = (v->curPlayer + 1)%3;
                prev_state[v->curPlayer] = playCard (prev_state[v->curPlayer], last_action);
                if (isFinished (prev_state))
                    p->finishNode = true;
                else
                {
                    for(EncodedCards action: DoudizhuState(prev_state[p->curPlayer], p->last_action).validActions())
                        p->childs.push_back(make_pair(action, (MCTNode*) NULL));
                }
                return p;
            }
        return NULL;
    };
    
    MCTNode* TreePolicy (MCTNode * v, vector<EncodedCards> & init_state)
    {
        while (!v->finishNode)
        {
            // v is not fully expanded
            if(v->nEval < v->childs.size() + 1)
                return expand(v, init_state);
            auto best_child = bestChild (v);
            init_state[v->curPlayer] = playCard(init_state[v->curPlayer], best_child.first);
            v = best_child.second;
        }
        return v;
    }
    
    double defaultPolicy (MCTNode * s, vector<EncodedCards> & curState, int myPos)
    {
        int actualPos = (s->curPlayer+1+myPos)%3;
        vector<int> myCard = encodedCardsToCardCountVector (curState[s->curPlayer]),
                    nextCard = encodedCardsToCardCountVector (curState[(s->curPlayer+1)%3]), 
                    prevCard = encodedCardsToCardCountVector (curState[(s->curPlayer+2)%3]);
        switch (actualPos)
        {
            case 0:
            case 1:
                return evaluate_global_situation (myCard, nextCard, prevCard, actualPos);
            case 2:
                return evaluate_global_situation (myCard, prevCard, nextCard, actualPos);
        }
        return 0;
    }
    
    void backUp (MCTNode *p, double delta, int myPos)
    {
        int originalPos = (p->curPlayer+1+myPos)%3, nowPos;
        nowPos = originalPos;
        while (p != NULL)
        {
            p->nEval ++;
            p->score += delta * (originalPos && nowPos ? 1.0 : -1.0);
            p = p->parent;
            nowPos = (nowPos + 2)%3;
        }
    }

    void deleteMCT (MCTNode *p)
    {
        queue<MCTNode*> q;
        q.push(p);
        while(!q.empty())
        {
            p = q.front(); q.pop();
            for (auto child_pair: p->childs)
                if(child_pair.second != NULL)
                    q.push(child_pair.second);
            delete(p);
        }
    }

    pair<EncodedCards, double> UCTSearch (const vector<EncodedCards> & init_state, EncodedCards lastAction, int myPos)
    {
        MCTNode *root = new MCTNode (lastAction), *ptr;
        double delta;
        root->curPlayer = 2; // Due to the sampling
        root->nEval = 1;
        for(EncodedCards action: DoudizhuState(init_state[root->curPlayer], lastAction).validActions())
            root->childs.push_back(make_pair(action, (MCTNode*) NULL));
        for (int i = 0; i < 100; i ++)
        {
            vector<EncodedCards> curState = init_state;
            ptr = TreePolicy (root, curState);   
            delta = defaultPolicy (ptr, curState, myPos); 
            backUp (ptr, delta, myPos);
        }
        auto ret = bestChild(root);
        delta = UCT(root, ret.second);
        deleteMCT(root);
        return make_pair(ret.first, delta);
    }

    bool compare (const pair<EncodedCards, pair<double, int> > & x, const pair<EncodedCards, pair<double, int> > & y)
    {
        return x.second < y.second;
    }

    EncodedCards DetMCTS (EncodedCards lastAction, int myPos)
    {
        map<EncodedCards, pair<double, int> > answers;
        for (int T = 0; T < 100; T ++)
        {
            vector<EncodedCards> init_state = sample ();
            auto answer = UCTSearch (init_state, lastAction, myPos);
            if (answers.count(answer.first))
            {
                auto prev_ans = answers[answer.first];
                answers[answer.first] = make_pair((prev_ans.first * (double) prev_ans.second + answer.second)/(double)(prev_ans.second+1), prev_ans.second+1);
            }
            else
                answers[answer.first] = make_pair(answer.second, 1);
        }
        return max_element(answers.begin(), answers.end(), compare)->first;
    }
}
void botzone()
{
    using namespace doudizhu;
    // 我的牌具体有哪些
    bool my_cards_bm[MAX_CARD_NUM] = {};
    bool player_cards_bm[3][MAX_CARD_NUM] = {};
    // 我的身份
    int pos;
    Json::Value input;
    Json::Reader reader;
    string line;
    getline(cin, line);
    reader.parse(line, input);
    // 这对大括号不要删掉
    {
        auto req = input["requests"][0u];
        auto own = req["own"];
        auto history = req["history"];
        // 标记一开始发给我的牌
        for (unsigned i = 0; i < own.size(); ++i)
        {
            my_cards_bm[own[i].asInt()] = true;
        }
        // pos对应了出牌的顺序
        if (history[0u].size() > 0)
        {
            pos = 2;
        }
        else if (history[1u].size() > 0)
        {
            pos = 1;
        }
        else
        {
            pos = 0;
        }
    }

    // 把我出过的牌从初始手牌中去掉
    for (unsigned i = 0; i < input["responses"].size(); ++i)
    {
        auto resp = input["responses"][i];
        for (unsigned j = 0; j < resp.size(); ++j)
        {
            my_cards_bm[resp[j].asInt()] = false;
        }
    }

    // 我当前实际拥有的牌、待响应的上一手牌（0-53编码）
    vector<Card> my_cards, last_action;
    for (int i = 0; i < MAX_CARD_NUM; ++i)
    {
        // 如果这牌我没出过，那么加入列表
        if (my_cards_bm[i])
        {
            my_cards.push_back(i);
        }
    }

    // 看看之前玩家出了什么牌
    auto history = input["requests"][input["requests"].size() - 1]["history"];
    if (history[1u].size() > 0)
    {
        for (unsigned i = 0; i < history[1u].size(); ++i)
        {
            int c = history[1u][i].asInt();
            last_action.push_back(c);
        }
    }
    else if (history[0u].size() > 0)
    {
        for (unsigned i = 0; i < history[0u].size(); ++i)
        {
            int c = history[0u][i].asInt();
            last_action.push_back(c);
        }
    }

    full_cards = encodedCardsToCardCountVector(FULL_CARDS);
    //从输入中提取出每一次三位玩家的出牌
    auto history_all_turn = input["requests"];
    turn = history_all_turn.size();
    player_a = (pos + 1) % 3, player_b = (pos + 2) % 3;
    for (unsigned i = 0; i < turn; i++)
    {
        EncodedCards combo_a = 0, combo_b = 0, combo_c = 0;
        if (i > 0 || pos == 2)
        {
            for (unsigned j = 0; j < history_all_turn[i]["history"][0u].size(); j++)
            {
                combo_a = addToEncodedCards(CardType(cardTypeOf(history_all_turn[i]["history"][0u][j].asInt())), combo_a, 1);
                player_cards_bm[player_a][history_all_turn[i]["history"][0u][j].asInt()] = true;
            }
            history_combo[(pos + 1) % 3].push_back(combo_a);
        }
        if (i > 0 || pos >= 1)
        {
            for (unsigned j = 0; j < history_all_turn[i]["history"][1u].size(); j++)
            {
                combo_b = addToEncodedCards(CardType(cardTypeOf(history_all_turn[i]["history"][1u][j].asInt())), combo_b, 1);
                player_cards_bm[player_b][history_all_turn[i]["history"][1u][j].asInt()] = true;
            }
            history_combo[(pos + 2) % 3].push_back(combo_b);
        }
        if (i != turn - 1)
        {
            for (unsigned int j = 0; j < input["responses"][i].size(); j++)
            {
                combo_c = addToEncodedCards(CardType(cardTypeOf(input["responses"][i][j].asInt())), combo_c, 1);
            }
            history_combo[pos].push_back(combo_c);
        }
    }
    //记录每一轮其他两人的需要压的牌，注意，last_action 在末尾可能会多加一些牌（因为没有判断末尾的边界
    history_last_action[0].push_back(0);
    for (unsigned int i = 0; i < turn; i++)
    {
        for (int player = 0; player < 3; player++)
        {
            int next_player = (player + 1) % 3, last_player = (player - 1) % 3;
            if (i < history_combo[player].size())
            {
                if (history_combo[player][i] > 0)
                {
                    history_last_action[next_player].push_back(history_combo[player][i]);
                    if (i + (next_player < player) < history_combo[next_player].size() && history_combo[next_player][i + (next_player < player)] == 0)
                    {
                        history_last_action[last_player].push_back(history_combo[player][i]);
                    }
                }
                else if (i + (next_player < player) < history_combo[next_player].size() && history_combo[next_player][i + (next_player < player)] == 0)
                {
                    history_last_action[last_player].push_back(EncodedCards(0));
                }
            }
        }
    }
    for (int i = 0; i < history_combo[player_a].size(); i++)
    {
        cards_played_a += history_combo[player_a][i];
    }
    for (int i = 0; i < history_combo[player_b].size(); i++)
    {
        cards_played_b += history_combo[player_b][i];
    }
    for(int i = 0; i < history_combo[pos].size(); i++){
        cards_played_c += history_combo[pos][i];
    }
    //处理地主公开牌
    for (int i = 0; i < 3; i++)
    {
        player_cards_bm[0][input["requests"][0u]["publiccard"][i].asInt()] = true;
    }
    //记录另外两位玩家所有已经打出去的手牌
    vector<Card> cards_a, cards_b;
    for (int i = 0; i < MAX_CARD_NUM; i++)
    {
        if (player_cards_bm[player_a][i])
            cards_a.push_back(i);
        if (player_cards_bm[player_b][i])
            cards_b.push_back(i);
    }
    EncodedCards encoded_known_cards_a = toEncodedCards(toCardCountVector(cards_a)), encoded_known_cards_b = toEncodedCards(toCardCountVector(cards_b));
    //记录自己的初始手牌
    auto own = input["requests"][0u]["own"];
    vector<Card> my_initial_cards;
    for (int i = 0; i < own.size(); i++)
    {
        my_initial_cards.push_back(own[i].asInt());
    }
    my_initial_cards_counter = toCardCountVector(my_initial_cards);
    encoded_my_initial_cards = toEncodedCards(my_initial_cards_counter);
    //记录所有目前还不知道在谁手中的牌
    unknown_cards = encodedCardsToCardCountVector(FULL_CARDS - encoded_known_cards_a - encoded_known_cards_b - encoded_my_initial_cards);

    vector<int> known_cards_a = encodedCardsToCardCountVector(encoded_known_cards_a);
    vector<int> known_cards_b = encodedCardsToCardCountVector(encoded_known_cards_b);
    //遍历所有的初始可能手牌，并计算其后验概率分布的cdf(存储在全局变量cumulative_probability 中)
    transverseAllHands(START_CARD, known_cards_a, known_cards_b);
    int tmp = cumulative_probability.size();
    for (int i = 0; i < tmp; i++)
        cumulative_probability[i] /= cumulative_probability[tmp - 1];
    /*
        //输出所有可能初始情况和概率
        for(int i = 0; i < tmp; i++)
            if (i) cout << cumulative_probability[i] - cumulative_probability[i-1] << " " << hex << (possible_hands_a[i]>>24) << endl;
            else cout << cumulative_probability[i] << " " << hex << (possible_hands_a[i]>>24) << endl;
    */
    // 根据我现有手牌、待响应的上一手牌，构造当前游戏状态
    DoudizhuState state(my_cards, last_action);

    // 根据当前游戏状态，生成全部可行动作，用EncodedCards编码
    vector<EncodedCards> valid_actions = state.validActions();
    // 随机选择得到的动作，用牌张列表表示（0-53编码）
    vector<Card> action;
    
    action = state.decodeAction(DetMCTS (toEncodedCards(toCardCountVector(last_action)), pos));
/*
    // 随机选择得到的动作在所有可行动作中的序号
    unsigned random_action_id;
    srand(time(nullptr));

    // 之前人都Pass了，我就得出牌，不能pass
    if (state.last_action.isPass())
    {
        random_action_id = rand() % valid_actions.size();
        action = state.decodeAction(valid_actions[random_action_id]);
    }
    else
    {
        // 之前人没有都Pass，我可以选择pass
        random_action_id = rand() % (valid_actions.size() + 1);
        // 此时我方动作选择不是pass，需要计算具体action
        if (random_action_id != valid_actions.size())
        {
            action = state.decodeAction(valid_actions[random_action_id]);
        }
    }
    */
    Json::Value result, response(Json::arrayValue);
    for (Card c : action)
    {
        response.append(c);
    }
    result["response"] = response;
    Json::FastWriter writer;
    cout << writer.write(result) << endl;
}

int main()
{
    //srand(time(0));
    srand(0);

    botzone();

    return 0;
}
