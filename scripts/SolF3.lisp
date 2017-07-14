(load "datastructures.lisp")
(load "auxfuncs.lisp")

;(load "datastructures.fas")
;(load "auxfuncs.fas")


;;; TAI position
(defun make-pos (c l)
  (list c l))
(defun pos-l (pos)
  (first pos))
(defun pos-c (pos)
  (second pos))

;;; TAI acceleration
(defun make-acce (c l)
  (list c l))
(defun acce-l (pos)
  (first pos))
(defun acce-c (pos)
  (second pos))

;;; TAI velocity
(defun make-vel (c l)
  (list c l))
(defun vel-l (pos)
  (first pos))
(defun vel-c (pos)
  (second pos))


;; Solution of phase 1

(defun getTrackContent (pos track)
  (nth (pos-c pos) (nth (pos-l pos) (track-env track))))

;; Pedir 0,4
(defun isObstaclep (pos track)
  "check if the position pos is an obstacle"
  (or (< (pos-l pos) 0) (< (pos-c pos) 0)
      (>= (pos-l pos) (pos-l (track-size track)))
      (>= (pos-c pos) (pos-c (track-size track)))
      (null (getTrackContent pos track))))

;; Pedir 0,4
(defun isGoalp (st) 
  "check if st is a solution of the problem"
  (let ((current-position (state-pos st))
	(track (state-track st)))
    (and (member current-position (track-endpositions track) :test #'equalp)
	 T)))

;; Pedir 1,2
(defun nextState (st act)
  "generate the nextState after state st and action act from prolem"
  (let ((new-state (make-state :action act :track (state-track st))))
    (setf (state-vel new-state)
	  (make-vel (+ (vel-l (state-vel st)) (acce-l act))
		    (+ (vel-c (state-vel st)) (acce-c act))))
    (setf (state-pos new-state)
	  (make-pos (+ (pos-l (state-pos st)) (vel-l (state-vel new-state)))
		    (+ (pos-c (state-pos st)) (vel-c (state-vel new-state)))))
    (setf (state-cost new-state)
	  (cond ((isGoalp new-state) -100)
		((isObstaclep (state-pos new-state) (state-track new-state)) 20)
		(T 1)))
    (when (= (state-cost new-state) 20)
      (setf (state-vel new-state) (make-vel 0 0))
      (setf (state-pos new-state) (make-pos (pos-l (state-pos st))
					    (pos-c (state-pos st)))))
    (values new-state)))

;; Solution of phase 2

;;; Pedir 
(defun nextStates (st)
  "generate all possible next states"
  (let ((successors nil))
    (dolist (act (possible-actions) successors)
      (let ((new-state (nextState st act)))
  (if (not (member new-state successors :test #'equalp))
      (push new-state successors))))))

;;; Solucao e uma seq ordenada de estados
(defun solution (node)
  (let ((seq-states nil))
    (loop 
      (when (null node)
  (return))
      (push (node-state node) seq-states)
      (setf node (node-parent node)))
    (values seq-states)))


;;; limdepthfirstsearch 
(defun limdepthfirstsearch (problem lim &key cutoff?)
  ;"limited depth first search
  ;   st - initial state
  ;   problem - problem information
  ;   lim - depth limit"
  (labels ((limdepthfirstsearch-aux (node problem lim)
       (if (isGoalp (node-state node))
     (solution node)
     (if (zerop lim)
         :cutoff
         (let ((cutoff? nil))
           (dolist (new-state (nextStates (node-state node)))
       (let* ((new-node (make-node :parent node :state new-state))
        (res (limdepthfirstsearch-aux new-node problem (1- lim))))
         (if (eq res :cutoff)
             (setf cutoff? :cutoff)
             (if (not (null res))
           (return-from limdepthfirstsearch-aux res)))))
           (values cutoff?))))))
    (let ((res (limdepthfirstsearch-aux (make-node :parent nil :state (problem-initial-state problem))
          problem
          lim)))
      (if (eq res :cutoff)
    (if cutoff?
        :cutoff
        nil)
    res))))
              

;iterlimdepthfirstsearch
(defun iterlimdepthfirstsearch (problem &key (lim most-positive-fixnum))
  ;"limited depth first search
  ;   st - initial state
  ;   problem - problem information
  ;   lim - limit of depth iterations"
  (let ((i 0))
    (loop
      (let ((res (limdepthfirstsearch problem i :cutoff? T)))
  (when (and res (not (eq res :cutoff)))
    (return res))
  (incf i)
  (if (> i lim)
      (return nil))))))
	
;; Solution of phase 3


(defun compute-heuristic(st)
  (let*((start (track-startpos (state-track st)))
        (current (state-pos st))
        (goals (track-endpositions(state-track st)))
        (result 50))
    (dolist (goal goals)
      (let*((dx1 (- (first current) (first goal)))
            (dy1 (- (second current) (second goal)))
            (dx2 (- (first start) (first goal)))
            (dy2 (- (second start) (second goal)))
            (cross (abs(- (* dx1 dy2) (* dx2 dy1)))))
        (if (< (* cross 0.001) result)
          (setf result (* cross 0.001)))))
    result))





;; Heuristic
(defun compute-heuristic-orig (st)
  (let*((start (state-pos st))
       ;(lstart (first start))
       ;(cstart (second start))
       (finals (track-endpositions (state-track st)))
       (result 50))
    (dolist (pos finals)
      (let*((dx (abs (- (first start) (first pos))))
            (dy (abs (- (second start) (second pos))))
            (cost (- (+ dx dy) (min dx dy))))
        (if (< cost result)
          (setf result cost))))
    result))
	  
  

(defun a* (problem)
  (let*((open nil)
       (closed nil)
       (node (make-node :state (problem-initial-state problem) :f nil
        :g 0 :h (compute-heuristic (problem-initial-state problem))))
       (successors nil))
  (set-f node)
  (push node open)
  (loop while (not (null open))
  do
    (setf node (select-best open))
    (setf open(remove node open))
    (setf successors (funcall (problem-fn-nextStates problem) (node-state node)))
  (dolist (elem successors)
        (let* ((successor (make-node :parent node :state elem)))
          (cond ((funcall (problem-fn-isGoal problem) (node-state successor)) (return-from a* (solution successor))))
          (setf (node-g successor) (+ (node-g (node-parent successor)) (state-cost(node-state successor))))
          (setf (node-h successor) (compute-heuristic (node-state successor)))
          (setf (node-f successor) (+ (node-g successor) (node-h successor)))
    
    (cond((or (and(equal (state-pos (node-state node)) (state-pos (node-state successor))) (< (node-f node) (node-f successor)) (when(not(null(find successor open :test #'equal)))T))
          (and(equal (state-pos (node-state node)) (state-pos (node-state successor))) (< (node-f node) (node-f successor)) (when(not(null(find successor closed :test #'equal)))T))))
      (t (push successor open)))))
     (push node closed))))
	  
;calcula valor f
(defun set-f (node)
  (setf (node-f node) (+ (node-g node) (node-h node)))
)

;;; SELECT-BEST chooses a node in step 3...
(defun select-best (lst)
  (let*((value-f 50)
       (node (first lst)))
  (dolist (elem lst)
    (if(< (node-f elem) value-f)
      (progn
        (setf value-f (node-f elem))
        (setf node elem))))
  node))

; transformar estados para nos
(defun states-to-nodes (states node)
  (let((nodes nil))
  (dolist (elem states)
    (push (make-node :parent node :state elem) nodes))
  nodes))