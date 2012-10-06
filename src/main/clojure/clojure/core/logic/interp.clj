(ns clojure.core.logic.interp
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic))

(declare tracer trace-subst?)

;; to remove thunks
(defn unwrap [g]
  (cond
   (trace-subst? g) g
   (= (mk-exp g) :inc) (recur (g))
   :else  g))

(defprotocol ISearchTree
  (tree [this]))

;This stores the traced tree in the `_tree` member,
;and the seen goals in the `seen` member.
;
;n.b. `tracer` is a constructor function for
;`TraceSubstitutions`.
(deftype TraceSubstitutions [_tree seen]
  ISearchTree
  (tree [this] _tree)

  IBind
  (bind [this g]
    ;If we've already scanned the current goal, we can skip it
    ;We'll add a note to the `_tree` that we return that there
    ;was something here.
    (if (seen (class g))
      (tracer (conj _tree [:goal :seen]) seen)

      ;This branch means we haven't seen the goal, yet
      (let [exp (mk-exp g)

            ;Here, we try to form the subtree. We include
            ;special information about container goals,
            ;currently just `fresh` and `conde`. One
            ;could imagine `all` getting treated specially
            ;here, too.
            sub-tree (cond
                      (= exp :fresh) [exp (mk-vars g)]
                       ;This marks a branch of a conde
                      (= exp :conde) [:conde]
                       ;Currently, the only nofollow is unification
                      (= exp :nofollow) :==
                       ;This must be a collection to support `conj`
                       ;or else it errors out. Some
                      :else [:goal])

            ;This is a substitution we can pass along to the child
            sub-s (tracer sub-tree (conj seen (class g)))

            [tree' seen'] (if (= exp :nofollow)
                            ;Don't descend on a no-follow
                            [sub-tree seen]
                            ;Here, we descend through the children
                            ;and record the new subtree and what they saw
                            ;so that we don't re-follow a grandchild
                            (->> (g sub-s)
                              unwrap
                              ((juxt #(._tree %)
                                     #(.seen %))))) 

            ;`tree'` only included the subtree--we must add it to
            ;the current tree
            tree' (conj _tree tree')]
        (tracer tree' seen'))))

  IMPlus
  (mplus [this f]
    ;Again, we only follow mpluses we haven't seen yet
    ;This code is nearly identical to the bind implementation
    (if (seen (class f))
      (tracer (conj _tree [:mplus :seen] seen))
      (let [[tree' seen'] (->> (unwrap (f))
                            ((juxt #(._tree %)
                                   #(.seen %))))]
        (tracer [:mplus _tree tree'] (into seen seen'))))))

(defn tracer
  ([] (tracer [] #{}))
  ([tree] (tracer tree #{}))
  ([tree seen]
     (TraceSubstitutions. tree seen)))

(defn trace-subst? [x]
  (instance? TraceSubstitutions x))

;;Perhaps a safe and unsafe -inc are needed. Then one could explore
;;safe streams but not go into `project`ed functions or otherwise.

(defmethod clojure.core/print-method TraceSubstitutions
  [^TraceSubstitutions o ^java.io.Writer w]
  (.write w "TraceSubstitutions(")
  (clojure.core/print-method (._tree o) w) 
  (.write w ", ")
  (clojure.core/print-method (.seen o) w)
  (.write w ")"))

( comment) 
  ; ; works
  (tree (bind (bind (tracer) s#) s#)) 

  ; ; works
  (tree (bind (tracer) (fresh [x] s# s#))) 

  ; ; works
  (tree (bind (tracer) (fresh [x] (fresh [y] s#) s#))) 

  ; ; works
  (clojure.pprint/pprint (tree
   (bind (tracer)
           (conde
             [s# s#]
             [s# s#])
         )))

  (tree
    (bind (tracer)
                 (== (lvar) 3))) 

  (defn bar []
    (conde
      [s#]
      [s#])) 

  (defn foo []
    (fresh [x y]
      s#
      (bar))) 

  ; ; can trace relations
  (tree (bind (tracer) (foo))) 

  (defn aloop [x]
    (conde
      [(== x 3)]
      [(aloop (lvar))])) 

  ; ; works can handle recursive goals
  (tree (bind (tracer) (aloop (lvar))))

   
  ;; 1. we care about fresh
  ;; 2. we care about conde
  ;; 3. if encounter -inc, we force it
  ;; 4. we never call goals we've seen before
  ;; 5. we can test whether two goal are the same, their classes will match
  ; ;    this works for regular relations, ones that don't using matching sugar

(defne righto  [x y l]
    ([_ _  [x y . ?r]])
    ([_ _  [_ . ?r]]  (righto x y ?r)))

(clojure.core/defn righto [x y l]
  (clojure.core.logic/conde
    ((clojure.core.logic/fresh
       [?r]
       (clojure.core.logic/== (clojure.core.logic/llist x y ?r) l)))
    ((clojure.core.logic/fresh
       [?r]
       (clojure.core.logic/==
         (clojure.core.logic/llist (clojure.core.logic/lvar) ?r)
         l)
       (righto x y ?r)))))

(clojure.core/defn righto [x y l]
  (clojure.core/reify
    clojure.lang.IFn
    (invoke
      [this__3128__auto__ a29885]
      (clojure.core.logic/-inc
        (clojure.core.logic/mplus*
          (clojure.core.logic/bind*
            a29885
            (clojure.core.logic/fresh
              [?r]
              (clojure.core.logic/==
                (clojure.core.logic/llist x y ?r)
                l)))
          (clojure.core.logic/bind*
            a29885
            (clojure.core/let [?r (clojure.core.logic/lvar '?r)]
              (clojure.core/reify
                clojure.lang.IFn
                (invoke
                  [this__3138__auto__ a__3139__auto__]
                  (clojure.core.logic/-inc
                    (clojure.core.logic/bind
                      (clojure.core.logic/bind
                        a__3139__auto__
                        (clojure.core.logic/==
                          (clojure.core.logic/llist (clojure.core.logic/lvar) ?r)
                          l))
                      (righto x y ?r))))
                clojure.core.logic/IMKExp
                (clojure.core.logic/mk-exp [this__3138__auto__] :fresh)
                clojure.core.logic/IMKVars
                (clojure.core.logic/mk-vars [this__3138__auto__] [?r])))))))
    clojure.core.logic/IMKExp
    (clojure.core.logic/mk-exp [this__3128__auto__] :conde)))
(defn nexto  [x y l]
  (conde
    ((righto x y l))
    ((righto y x l)))) 
(defn zebrao  [hs]

  (all
    (==  [(lvar) (lvar)  [(lvar) (lvar) 'milk (lvar) (lvar)] (lvar) (lvar)] hs)                         
    (firsto hs  ['norwegian (lvar) (lvar) (lvar) (lvar)])                         
    (nexto  ['norwegian (lvar) (lvar) (lvar) (lvar)]  [(lvar) (lvar) (lvar) (lvar) 'blue] hs)       
    (righto  [(lvar) (lvar) (lvar) (lvar) 'ivory]  [(lvar) (lvar) (lvar) (lvar) 'green] hs)         
    (membero  ['englishman (lvar) (lvar) (lvar) 'red] hs)                    
    (membero  [(lvar) 'kools (lvar) (lvar) 'yellow] hs)                      
    (membero  ['spaniard (lvar) (lvar) 'dog (lvar)] hs)                      
    (membero  [(lvar) (lvar) 'coffee (lvar) 'green] hs)                      
    (membero  ['ukrainian (lvar) 'tea (lvar) (lvar)] hs)           ))

(try (clojure.pprint/pprint
       (tree (clojure.core.logic/bind
               (tracer)
               (zebrao (lvar)))))
  (catch Exception e (.printStackTrace e)))

