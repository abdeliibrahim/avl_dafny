def build_lcp_array(S, SA):
    """
    Constructs the LCP array for string S given its Suffix Array SA using brute-force.

    Parameters:
        S (str): The original string.
        SA (list[int]): The suffix array of S.

    Returns:
        list[int]: The LCP array.
    """
    n = len(S)
    LCP = [0]  # First LCP is always 0 by definition
    for i in range(1, n):
        l = SA[i-1]
        r = SA[i]
        count = 0
        while l < n and r < n and S[l] == S[r]:
            l += 1
            r += 1
            count += 1
        LCP.append(count)
    return LCP

# Example usage:
S = "banana"
# Suffix array for "banana" (for reference):
# 5: "a"
# 3: "ana"
# 1: "anana"
# 0: "banana"
# 4: "na"
# 2: "nana"
SA = [5, 3, 1, 0, 4, 2]

lcp = build_lcp_array(S, SA)
print(lcp)  # Output: [0, 1, 3, 0, 0, 2]
